open Prims
type goal = FStar_Tactics_Types.goal[@@deriving show]
type name = FStar_Syntax_Syntax.bv[@@deriving show]
type env = FStar_TypeChecker_Env.env[@@deriving show]
type implicits = FStar_TypeChecker_Env.implicits[@@deriving show]
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
[@@deriving show]
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
                 let uu___93_1004 = ps  in
                 {
                   FStar_Tactics_Types.main_context =
                     (uu___93_1004.FStar_Tactics_Types.main_context);
                   FStar_Tactics_Types.main_goal =
                     (uu___93_1004.FStar_Tactics_Types.main_goal);
                   FStar_Tactics_Types.all_implicits =
                     (uu___93_1004.FStar_Tactics_Types.all_implicits);
                   FStar_Tactics_Types.goals =
                     (uu___93_1004.FStar_Tactics_Types.goals);
                   FStar_Tactics_Types.smt_goals =
                     (uu___93_1004.FStar_Tactics_Types.smt_goals);
                   FStar_Tactics_Types.depth =
                     (uu___93_1004.FStar_Tactics_Types.depth);
                   FStar_Tactics_Types.__dump =
                     (uu___93_1004.FStar_Tactics_Types.__dump);
                   FStar_Tactics_Types.psc =
                     (uu___93_1004.FStar_Tactics_Types.psc);
                   FStar_Tactics_Types.entry_range =
                     (uu___93_1004.FStar_Tactics_Types.entry_range);
                   FStar_Tactics_Types.guard_policy =
                     (uu___93_1004.FStar_Tactics_Types.guard_policy);
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
         let uu___98_1306 = p  in
         let uu____1307 = FStar_List.tl p.FStar_Tactics_Types.goals  in
         {
           FStar_Tactics_Types.main_context =
             (uu___98_1306.FStar_Tactics_Types.main_context);
           FStar_Tactics_Types.main_goal =
             (uu___98_1306.FStar_Tactics_Types.main_goal);
           FStar_Tactics_Types.all_implicits =
             (uu___98_1306.FStar_Tactics_Types.all_implicits);
           FStar_Tactics_Types.goals = uu____1307;
           FStar_Tactics_Types.smt_goals =
             (uu___98_1306.FStar_Tactics_Types.smt_goals);
           FStar_Tactics_Types.depth =
             (uu___98_1306.FStar_Tactics_Types.depth);
           FStar_Tactics_Types.__dump =
             (uu___98_1306.FStar_Tactics_Types.__dump);
           FStar_Tactics_Types.psc = (uu___98_1306.FStar_Tactics_Types.psc);
           FStar_Tactics_Types.entry_range =
             (uu___98_1306.FStar_Tactics_Types.entry_range);
           FStar_Tactics_Types.guard_policy =
             (uu___98_1306.FStar_Tactics_Types.guard_policy);
           FStar_Tactics_Types.freshness =
             (uu___98_1306.FStar_Tactics_Types.freshness)
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
      let uu____1340 = trysolve goal solution  in
      bind uu____1340
        (fun b  ->
           if b
           then __dismiss
           else
             (let uu____1348 =
                let uu____1349 =
                  tts goal.FStar_Tactics_Types.context solution  in
                let uu____1350 =
                  tts goal.FStar_Tactics_Types.context
                    goal.FStar_Tactics_Types.witness
                   in
                let uu____1351 =
                  tts goal.FStar_Tactics_Types.context
                    goal.FStar_Tactics_Types.goal_ty
                   in
                FStar_Util.format3 "%s does not solve %s : %s" uu____1349
                  uu____1350 uu____1351
                 in
              fail uu____1348))
  
let (dismiss_all : unit tac) =
  bind get
    (fun p  ->
       set
         (let uu___99_1358 = p  in
          {
            FStar_Tactics_Types.main_context =
              (uu___99_1358.FStar_Tactics_Types.main_context);
            FStar_Tactics_Types.main_goal =
              (uu___99_1358.FStar_Tactics_Types.main_goal);
            FStar_Tactics_Types.all_implicits =
              (uu___99_1358.FStar_Tactics_Types.all_implicits);
            FStar_Tactics_Types.goals = [];
            FStar_Tactics_Types.smt_goals =
              (uu___99_1358.FStar_Tactics_Types.smt_goals);
            FStar_Tactics_Types.depth =
              (uu___99_1358.FStar_Tactics_Types.depth);
            FStar_Tactics_Types.__dump =
              (uu___99_1358.FStar_Tactics_Types.__dump);
            FStar_Tactics_Types.psc = (uu___99_1358.FStar_Tactics_Types.psc);
            FStar_Tactics_Types.entry_range =
              (uu___99_1358.FStar_Tactics_Types.entry_range);
            FStar_Tactics_Types.guard_policy =
              (uu___99_1358.FStar_Tactics_Types.guard_policy);
            FStar_Tactics_Types.freshness =
              (uu___99_1358.FStar_Tactics_Types.freshness)
          }))
  
let (nwarn : Prims.int FStar_ST.ref) =
  FStar_Util.mk_ref (Prims.parse_int "0") 
let (check_valid_goal : FStar_Tactics_Types.goal -> unit) =
  fun g  ->
    let uu____1377 = FStar_Options.defensive ()  in
    if uu____1377
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
        let uu____1393 = FStar_TypeChecker_Env.pop_bv e  in
        match uu____1393 with
        | FStar_Pervasives_Native.None  -> b3
        | FStar_Pervasives_Native.Some (bv,e1) ->
            let b4 =
              b3 &&
                (FStar_TypeChecker_Env.closed e1 bv.FStar_Syntax_Syntax.sort)
               in
            aux b4 e1
         in
      let uu____1411 =
        (let uu____1414 = aux b2 env  in Prims.op_Negation uu____1414) &&
          (let uu____1416 = FStar_ST.op_Bang nwarn  in
           uu____1416 < (Prims.parse_int "5"))
         in
      (if uu____1411
       then
         ((let uu____1441 =
             let uu____1446 =
               let uu____1447 = goal_to_string g  in
               FStar_Util.format1
                 "The following goal is ill-formed. Keeping calm and carrying on...\n<%s>\n\n"
                 uu____1447
                in
             (FStar_Errors.Warning_IllFormedGoal, uu____1446)  in
           FStar_Errors.log_issue
             (g.FStar_Tactics_Types.goal_ty).FStar_Syntax_Syntax.pos
             uu____1441);
          (let uu____1448 =
             let uu____1449 = FStar_ST.op_Bang nwarn  in
             uu____1449 + (Prims.parse_int "1")  in
           FStar_ST.op_Colon_Equals nwarn uu____1448))
       else ())
    else ()
  
let (add_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___100_1517 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___100_1517.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___100_1517.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___100_1517.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (FStar_List.append gs p.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___100_1517.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___100_1517.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___100_1517.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___100_1517.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___100_1517.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___100_1517.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___100_1517.FStar_Tactics_Types.freshness)
            }))
  
let (add_smt_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___101_1537 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___101_1537.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___101_1537.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___101_1537.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___101_1537.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (FStar_List.append gs p.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___101_1537.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___101_1537.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___101_1537.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___101_1537.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___101_1537.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___101_1537.FStar_Tactics_Types.freshness)
            }))
  
let (push_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___102_1557 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___102_1557.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___102_1557.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___102_1557.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (FStar_List.append p.FStar_Tactics_Types.goals gs);
              FStar_Tactics_Types.smt_goals =
                (uu___102_1557.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___102_1557.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___102_1557.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___102_1557.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___102_1557.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___102_1557.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___102_1557.FStar_Tactics_Types.freshness)
            }))
  
let (push_smt_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___103_1577 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___103_1577.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___103_1577.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___103_1577.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___103_1577.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (FStar_List.append p.FStar_Tactics_Types.smt_goals gs);
              FStar_Tactics_Types.depth =
                (uu___103_1577.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___103_1577.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___103_1577.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___103_1577.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___103_1577.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___103_1577.FStar_Tactics_Types.freshness)
            }))
  
let (replace_cur : FStar_Tactics_Types.goal -> unit tac) =
  fun g  -> bind __dismiss (fun uu____1588  -> add_goals [g]) 
let (add_implicits : implicits -> unit tac) =
  fun i  ->
    bind get
      (fun p  ->
         set
           (let uu___104_1602 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___104_1602.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___104_1602.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (FStar_List.append i p.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___104_1602.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___104_1602.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___104_1602.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___104_1602.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___104_1602.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___104_1602.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___104_1602.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___104_1602.FStar_Tactics_Types.freshness)
            }))
  
let (new_uvar :
  Prims.string ->
    env -> FStar_Reflection_Data.typ -> FStar_Syntax_Syntax.term tac)
  =
  fun reason  ->
    fun env  ->
      fun typ  ->
        let uu____1632 =
          FStar_TypeChecker_Util.new_implicit_var reason
            typ.FStar_Syntax_Syntax.pos env typ
           in
        match uu____1632 with
        | (u,uu____1648,g_u) ->
            let uu____1662 =
              add_implicits g_u.FStar_TypeChecker_Env.implicits  in
            bind uu____1662 (fun uu____1666  -> ret u)
  
let (is_true : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____1672 = FStar_Syntax_Util.un_squash t  in
    match uu____1672 with
    | FStar_Pervasives_Native.Some t' ->
        let uu____1682 =
          let uu____1683 = FStar_Syntax_Subst.compress t'  in
          uu____1683.FStar_Syntax_Syntax.n  in
        (match uu____1682 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.true_lid
         | uu____1687 -> false)
    | uu____1688 -> false
  
let (is_false : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____1698 = FStar_Syntax_Util.un_squash t  in
    match uu____1698 with
    | FStar_Pervasives_Native.Some t' ->
        let uu____1708 =
          let uu____1709 = FStar_Syntax_Subst.compress t'  in
          uu____1709.FStar_Syntax_Syntax.n  in
        (match uu____1708 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.false_lid
         | uu____1713 -> false)
    | uu____1714 -> false
  
let (cur_goal : unit -> FStar_Tactics_Types.goal tac) =
  fun uu____1725  ->
    bind get
      (fun p  ->
         match p.FStar_Tactics_Types.goals with
         | [] -> fail "No more goals (1)"
         | hd1::tl1 -> ret hd1)
  
let (tadmit : unit -> unit tac) =
  fun uu____1742  ->
    let uu____1745 =
      let uu____1748 = cur_goal ()  in
      bind uu____1748
        (fun g  ->
           (let uu____1755 =
              let uu____1760 =
                let uu____1761 = goal_to_string g  in
                FStar_Util.format1 "Tactics admitted goal <%s>\n\n"
                  uu____1761
                 in
              (FStar_Errors.Warning_TacAdmit, uu____1760)  in
            FStar_Errors.log_issue
              (g.FStar_Tactics_Types.goal_ty).FStar_Syntax_Syntax.pos
              uu____1755);
           solve g FStar_Syntax_Util.exp_unit)
       in
    FStar_All.pipe_left (wrap_err "tadmit") uu____1745
  
let (fresh : unit -> FStar_BigInt.t tac) =
  fun uu____1772  ->
    bind get
      (fun ps  ->
         let n1 = ps.FStar_Tactics_Types.freshness  in
         let ps1 =
           let uu___105_1782 = ps  in
           {
             FStar_Tactics_Types.main_context =
               (uu___105_1782.FStar_Tactics_Types.main_context);
             FStar_Tactics_Types.main_goal =
               (uu___105_1782.FStar_Tactics_Types.main_goal);
             FStar_Tactics_Types.all_implicits =
               (uu___105_1782.FStar_Tactics_Types.all_implicits);
             FStar_Tactics_Types.goals =
               (uu___105_1782.FStar_Tactics_Types.goals);
             FStar_Tactics_Types.smt_goals =
               (uu___105_1782.FStar_Tactics_Types.smt_goals);
             FStar_Tactics_Types.depth =
               (uu___105_1782.FStar_Tactics_Types.depth);
             FStar_Tactics_Types.__dump =
               (uu___105_1782.FStar_Tactics_Types.__dump);
             FStar_Tactics_Types.psc =
               (uu___105_1782.FStar_Tactics_Types.psc);
             FStar_Tactics_Types.entry_range =
               (uu___105_1782.FStar_Tactics_Types.entry_range);
             FStar_Tactics_Types.guard_policy =
               (uu___105_1782.FStar_Tactics_Types.guard_policy);
             FStar_Tactics_Types.freshness = (n1 + (Prims.parse_int "1"))
           }  in
         let uu____1783 = set ps1  in
         bind uu____1783
           (fun uu____1788  ->
              let uu____1789 = FStar_BigInt.of_int_fs n1  in ret uu____1789))
  
let (ngoals : unit -> FStar_BigInt.t tac) =
  fun uu____1796  ->
    bind get
      (fun ps  ->
         let n1 = FStar_List.length ps.FStar_Tactics_Types.goals  in
         let uu____1804 = FStar_BigInt.of_int_fs n1  in ret uu____1804)
  
let (ngoals_smt : unit -> FStar_BigInt.t tac) =
  fun uu____1817  ->
    bind get
      (fun ps  ->
         let n1 = FStar_List.length ps.FStar_Tactics_Types.smt_goals  in
         let uu____1825 = FStar_BigInt.of_int_fs n1  in ret uu____1825)
  
let (is_guard : unit -> Prims.bool tac) =
  fun uu____1838  ->
    let uu____1841 = cur_goal ()  in
    bind uu____1841 (fun g  -> ret g.FStar_Tactics_Types.is_guard)
  
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
            let uu____1873 = env.FStar_TypeChecker_Env.universe_of env phi
               in
            FStar_Syntax_Util.mk_squash uu____1873 phi  in
          let uu____1874 = new_uvar reason env typ  in
          bind uu____1874
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
             (fun uu____1923  ->
                let uu____1924 = tts e t  in
                FStar_Util.print1 "Tac> __tc(%s)\n" uu____1924)
             (fun uu____1926  ->
                try
                  let uu____1946 =
                    (ps.FStar_Tactics_Types.main_context).FStar_TypeChecker_Env.type_of
                      e t
                     in
                  ret uu____1946
                with
                | FStar_Errors.Err (uu____1973,msg) ->
                    let uu____1975 = tts e t  in
                    let uu____1976 =
                      let uu____1977 = FStar_TypeChecker_Env.all_binders e
                         in
                      FStar_All.pipe_right uu____1977
                        (FStar_Syntax_Print.binders_to_string ", ")
                       in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____1975 uu____1976 msg
                | FStar_Errors.Error (uu____1984,msg,uu____1986) ->
                    let uu____1987 = tts e t  in
                    let uu____1988 =
                      let uu____1989 = FStar_TypeChecker_Env.all_binders e
                         in
                      FStar_All.pipe_right uu____1989
                        (FStar_Syntax_Print.binders_to_string ", ")
                       in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____1987 uu____1988 msg))
  
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
  fun uu____2016  ->
    bind get (fun ps  -> ret ps.FStar_Tactics_Types.guard_policy)
  
let (set_guard_policy : FStar_Tactics_Types.guard_policy -> unit tac) =
  fun pol  ->
    bind get
      (fun ps  ->
         set
           (let uu___108_2034 = ps  in
            {
              FStar_Tactics_Types.main_context =
                (uu___108_2034.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___108_2034.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___108_2034.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___108_2034.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___108_2034.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___108_2034.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___108_2034.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___108_2034.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___108_2034.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy = pol;
              FStar_Tactics_Types.freshness =
                (uu___108_2034.FStar_Tactics_Types.freshness)
            }))
  
let with_policy : 'a . FStar_Tactics_Types.guard_policy -> 'a tac -> 'a tac =
  fun pol  ->
    fun t  ->
      let uu____2058 = get_guard_policy ()  in
      bind uu____2058
        (fun old_pol  ->
           let uu____2064 = set_guard_policy pol  in
           bind uu____2064
             (fun uu____2068  ->
                bind t
                  (fun r  ->
                     let uu____2072 = set_guard_policy old_pol  in
                     bind uu____2072 (fun uu____2076  -> ret r))))
  
let (proc_guard :
  Prims.string ->
    env ->
      FStar_TypeChecker_Env.guard_t -> FStar_Options.optionstate -> unit tac)
  =
  fun reason  ->
    fun e  ->
      fun g  ->
        fun opts  ->
          let uu____2101 =
            let uu____2102 = FStar_TypeChecker_Rel.simplify_guard e g  in
            uu____2102.FStar_TypeChecker_Env.guard_f  in
          match uu____2101 with
          | FStar_TypeChecker_Common.Trivial  -> ret ()
          | FStar_TypeChecker_Common.NonTrivial f ->
              let uu____2106 = istrivial e f  in
              if uu____2106
              then ret ()
              else
                bind get
                  (fun ps  ->
                     match ps.FStar_Tactics_Types.guard_policy with
                     | FStar_Tactics_Types.Drop  -> ret ()
                     | FStar_Tactics_Types.Goal  ->
                         let uu____2114 = mk_irrelevant_goal reason e f opts
                            in
                         bind uu____2114
                           (fun goal  ->
                              let goal1 =
                                let uu___109_2121 = goal  in
                                {
                                  FStar_Tactics_Types.context =
                                    (uu___109_2121.FStar_Tactics_Types.context);
                                  FStar_Tactics_Types.witness =
                                    (uu___109_2121.FStar_Tactics_Types.witness);
                                  FStar_Tactics_Types.goal_ty =
                                    (uu___109_2121.FStar_Tactics_Types.goal_ty);
                                  FStar_Tactics_Types.opts =
                                    (uu___109_2121.FStar_Tactics_Types.opts);
                                  FStar_Tactics_Types.is_guard = true
                                }  in
                              push_goals [goal1])
                     | FStar_Tactics_Types.SMT  ->
                         let uu____2122 = mk_irrelevant_goal reason e f opts
                            in
                         bind uu____2122
                           (fun goal  ->
                              let goal1 =
                                let uu___110_2129 = goal  in
                                {
                                  FStar_Tactics_Types.context =
                                    (uu___110_2129.FStar_Tactics_Types.context);
                                  FStar_Tactics_Types.witness =
                                    (uu___110_2129.FStar_Tactics_Types.witness);
                                  FStar_Tactics_Types.goal_ty =
                                    (uu___110_2129.FStar_Tactics_Types.goal_ty);
                                  FStar_Tactics_Types.opts =
                                    (uu___110_2129.FStar_Tactics_Types.opts);
                                  FStar_Tactics_Types.is_guard = true
                                }  in
                              push_smt_goals [goal1])
                     | FStar_Tactics_Types.Force  ->
                         (try
                            let uu____2137 =
                              let uu____2138 =
                                let uu____2139 =
                                  FStar_TypeChecker_Rel.discharge_guard_no_smt
                                    e g
                                   in
                                FStar_All.pipe_left
                                  FStar_TypeChecker_Rel.is_trivial uu____2139
                                 in
                              Prims.op_Negation uu____2138  in
                            if uu____2137
                            then
                              mlog
                                (fun uu____2144  ->
                                   let uu____2145 =
                                     FStar_TypeChecker_Rel.guard_to_string e
                                       g
                                      in
                                   FStar_Util.print1 "guard = %s\n"
                                     uu____2145)
                                (fun uu____2147  ->
                                   fail1 "Forcing the guard failed %s)"
                                     reason)
                            else ret ()
                          with
                          | uu____2154 ->
                              mlog
                                (fun uu____2157  ->
                                   let uu____2158 =
                                     FStar_TypeChecker_Rel.guard_to_string e
                                       g
                                      in
                                   FStar_Util.print1 "guard = %s\n"
                                     uu____2158)
                                (fun uu____2160  ->
                                   fail1 "Forcing the guard failed (%s)"
                                     reason)))
  
let (tc : FStar_Syntax_Syntax.term -> FStar_Reflection_Data.typ tac) =
  fun t  ->
    let uu____2170 =
      let uu____2173 = cur_goal ()  in
      bind uu____2173
        (fun goal  ->
           let uu____2179 = __tc goal.FStar_Tactics_Types.context t  in
           bind uu____2179
             (fun uu____2199  ->
                match uu____2199 with
                | (t1,typ,guard) ->
                    let uu____2211 =
                      proc_guard "tc" goal.FStar_Tactics_Types.context guard
                        goal.FStar_Tactics_Types.opts
                       in
                    bind uu____2211 (fun uu____2215  -> ret typ)))
       in
    FStar_All.pipe_left (wrap_err "tc") uu____2170
  
let (add_irrelevant_goal :
  Prims.string ->
    env -> FStar_Reflection_Data.typ -> FStar_Options.optionstate -> unit tac)
  =
  fun reason  ->
    fun env  ->
      fun phi  ->
        fun opts  ->
          let uu____2244 = mk_irrelevant_goal reason env phi opts  in
          bind uu____2244 (fun goal  -> add_goals [goal])
  
let (trivial : unit -> unit tac) =
  fun uu____2255  ->
    let uu____2258 = cur_goal ()  in
    bind uu____2258
      (fun goal  ->
         let uu____2264 =
           istrivial goal.FStar_Tactics_Types.context
             goal.FStar_Tactics_Types.goal_ty
            in
         if uu____2264
         then solve goal FStar_Syntax_Util.exp_unit
         else
           (let uu____2268 =
              tts goal.FStar_Tactics_Types.context
                goal.FStar_Tactics_Types.goal_ty
               in
            fail1 "Not a trivial goal: %s" uu____2268))
  
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
          let uu____2297 =
            let uu____2298 = FStar_TypeChecker_Rel.simplify_guard e g  in
            uu____2298.FStar_TypeChecker_Env.guard_f  in
          match uu____2297 with
          | FStar_TypeChecker_Common.Trivial  ->
              ret FStar_Pervasives_Native.None
          | FStar_TypeChecker_Common.NonTrivial f ->
              let uu____2306 = istrivial e f  in
              if uu____2306
              then ret FStar_Pervasives_Native.None
              else
                (let uu____2314 = mk_irrelevant_goal reason e f opts  in
                 bind uu____2314
                   (fun goal  ->
                      ret
                        (FStar_Pervasives_Native.Some
                           (let uu___113_2324 = goal  in
                            {
                              FStar_Tactics_Types.context =
                                (uu___113_2324.FStar_Tactics_Types.context);
                              FStar_Tactics_Types.witness =
                                (uu___113_2324.FStar_Tactics_Types.witness);
                              FStar_Tactics_Types.goal_ty =
                                (uu___113_2324.FStar_Tactics_Types.goal_ty);
                              FStar_Tactics_Types.opts =
                                (uu___113_2324.FStar_Tactics_Types.opts);
                              FStar_Tactics_Types.is_guard = true
                            }))))
  
let (smt : unit -> unit tac) =
  fun uu____2331  ->
    let uu____2334 = cur_goal ()  in
    bind uu____2334
      (fun g  ->
         let uu____2340 = is_irrelevant g  in
         if uu____2340
         then bind __dismiss (fun uu____2344  -> add_smt_goals [g])
         else
           (let uu____2346 =
              tts g.FStar_Tactics_Types.context g.FStar_Tactics_Types.goal_ty
               in
            fail1 "goal is not irrelevant: cannot dispatch to smt (%s)"
              uu____2346))
  
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
             let uu____2395 =
               try
                 let uu____2429 =
                   let uu____2438 = FStar_BigInt.to_int_fs n1  in
                   FStar_List.splitAt uu____2438 p.FStar_Tactics_Types.goals
                    in
                 ret uu____2429
               with | uu____2460 -> fail "divide: not enough goals"  in
             bind uu____2395
               (fun uu____2487  ->
                  match uu____2487 with
                  | (lgs,rgs) ->
                      let lp =
                        let uu___114_2513 = p  in
                        {
                          FStar_Tactics_Types.main_context =
                            (uu___114_2513.FStar_Tactics_Types.main_context);
                          FStar_Tactics_Types.main_goal =
                            (uu___114_2513.FStar_Tactics_Types.main_goal);
                          FStar_Tactics_Types.all_implicits =
                            (uu___114_2513.FStar_Tactics_Types.all_implicits);
                          FStar_Tactics_Types.goals = lgs;
                          FStar_Tactics_Types.smt_goals = [];
                          FStar_Tactics_Types.depth =
                            (uu___114_2513.FStar_Tactics_Types.depth);
                          FStar_Tactics_Types.__dump =
                            (uu___114_2513.FStar_Tactics_Types.__dump);
                          FStar_Tactics_Types.psc =
                            (uu___114_2513.FStar_Tactics_Types.psc);
                          FStar_Tactics_Types.entry_range =
                            (uu___114_2513.FStar_Tactics_Types.entry_range);
                          FStar_Tactics_Types.guard_policy =
                            (uu___114_2513.FStar_Tactics_Types.guard_policy);
                          FStar_Tactics_Types.freshness =
                            (uu___114_2513.FStar_Tactics_Types.freshness)
                        }  in
                      let rp =
                        let uu___115_2515 = p  in
                        {
                          FStar_Tactics_Types.main_context =
                            (uu___115_2515.FStar_Tactics_Types.main_context);
                          FStar_Tactics_Types.main_goal =
                            (uu___115_2515.FStar_Tactics_Types.main_goal);
                          FStar_Tactics_Types.all_implicits =
                            (uu___115_2515.FStar_Tactics_Types.all_implicits);
                          FStar_Tactics_Types.goals = rgs;
                          FStar_Tactics_Types.smt_goals = [];
                          FStar_Tactics_Types.depth =
                            (uu___115_2515.FStar_Tactics_Types.depth);
                          FStar_Tactics_Types.__dump =
                            (uu___115_2515.FStar_Tactics_Types.__dump);
                          FStar_Tactics_Types.psc =
                            (uu___115_2515.FStar_Tactics_Types.psc);
                          FStar_Tactics_Types.entry_range =
                            (uu___115_2515.FStar_Tactics_Types.entry_range);
                          FStar_Tactics_Types.guard_policy =
                            (uu___115_2515.FStar_Tactics_Types.guard_policy);
                          FStar_Tactics_Types.freshness =
                            (uu___115_2515.FStar_Tactics_Types.freshness)
                        }  in
                      let uu____2516 = set lp  in
                      bind uu____2516
                        (fun uu____2524  ->
                           bind l
                             (fun a  ->
                                bind get
                                  (fun lp'  ->
                                     let uu____2538 = set rp  in
                                     bind uu____2538
                                       (fun uu____2546  ->
                                          bind r
                                            (fun b  ->
                                               bind get
                                                 (fun rp'  ->
                                                    let p' =
                                                      let uu___116_2562 = p
                                                         in
                                                      {
                                                        FStar_Tactics_Types.main_context
                                                          =
                                                          (uu___116_2562.FStar_Tactics_Types.main_context);
                                                        FStar_Tactics_Types.main_goal
                                                          =
                                                          (uu___116_2562.FStar_Tactics_Types.main_goal);
                                                        FStar_Tactics_Types.all_implicits
                                                          =
                                                          (uu___116_2562.FStar_Tactics_Types.all_implicits);
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
                                                          (uu___116_2562.FStar_Tactics_Types.depth);
                                                        FStar_Tactics_Types.__dump
                                                          =
                                                          (uu___116_2562.FStar_Tactics_Types.__dump);
                                                        FStar_Tactics_Types.psc
                                                          =
                                                          (uu___116_2562.FStar_Tactics_Types.psc);
                                                        FStar_Tactics_Types.entry_range
                                                          =
                                                          (uu___116_2562.FStar_Tactics_Types.entry_range);
                                                        FStar_Tactics_Types.guard_policy
                                                          =
                                                          (uu___116_2562.FStar_Tactics_Types.guard_policy);
                                                        FStar_Tactics_Types.freshness
                                                          =
                                                          (uu___116_2562.FStar_Tactics_Types.freshness)
                                                      }  in
                                                    let uu____2563 = set p'
                                                       in
                                                    bind uu____2563
                                                      (fun uu____2571  ->
                                                         ret (a, b))))))))))
  
let focus : 'a . 'a tac -> 'a tac =
  fun f  ->
    let uu____2592 = divide FStar_BigInt.one f idtac  in
    bind uu____2592
      (fun uu____2605  -> match uu____2605 with | (a,()) -> ret a)
  
let rec map : 'a . 'a tac -> 'a Prims.list tac =
  fun tau  ->
    bind get
      (fun p  ->
         match p.FStar_Tactics_Types.goals with
         | [] -> ret []
         | uu____2642::uu____2643 ->
             let uu____2646 =
               let uu____2655 = map tau  in
               divide FStar_BigInt.one tau uu____2655  in
             bind uu____2646
               (fun uu____2673  ->
                  match uu____2673 with | (h,t) -> ret (h :: t)))
  
let (seq : unit tac -> unit tac -> unit tac) =
  fun t1  ->
    fun t2  ->
      let uu____2714 =
        bind t1
          (fun uu____2719  ->
             let uu____2720 = map t2  in
             bind uu____2720 (fun uu____2728  -> ret ()))
         in
      focus uu____2714
  
let (intro : unit -> FStar_Syntax_Syntax.binder tac) =
  fun uu____2737  ->
    let uu____2740 =
      let uu____2743 = cur_goal ()  in
      bind uu____2743
        (fun goal  ->
           let uu____2752 =
             FStar_Syntax_Util.arrow_one goal.FStar_Tactics_Types.goal_ty  in
           match uu____2752 with
           | FStar_Pervasives_Native.Some (b,c) ->
               let uu____2767 =
                 let uu____2768 = FStar_Syntax_Util.is_total_comp c  in
                 Prims.op_Negation uu____2768  in
               if uu____2767
               then fail "Codomain is effectful"
               else
                 (let env' =
                    FStar_TypeChecker_Env.push_binders
                      goal.FStar_Tactics_Types.context [b]
                     in
                  let typ' = comp_to_typ c  in
                  let uu____2782 = new_uvar "intro" env' typ'  in
                  bind uu____2782
                    (fun u  ->
                       let uu____2788 =
                         let uu____2791 =
                           FStar_Syntax_Util.abs [b] u
                             FStar_Pervasives_Native.None
                            in
                         trysolve goal uu____2791  in
                       bind uu____2788
                         (fun bb  ->
                            if bb
                            then
                              let uu____2805 =
                                let uu____2808 =
                                  let uu___119_2809 = goal  in
                                  let uu____2810 = bnorm env' u  in
                                  let uu____2811 = bnorm env' typ'  in
                                  {
                                    FStar_Tactics_Types.context = env';
                                    FStar_Tactics_Types.witness = uu____2810;
                                    FStar_Tactics_Types.goal_ty = uu____2811;
                                    FStar_Tactics_Types.opts =
                                      (uu___119_2809.FStar_Tactics_Types.opts);
                                    FStar_Tactics_Types.is_guard =
                                      (uu___119_2809.FStar_Tactics_Types.is_guard)
                                  }  in
                                replace_cur uu____2808  in
                              bind uu____2805 (fun uu____2813  -> ret b)
                            else fail "unification failed")))
           | FStar_Pervasives_Native.None  ->
               let uu____2819 =
                 tts goal.FStar_Tactics_Types.context
                   goal.FStar_Tactics_Types.goal_ty
                  in
               fail1 "goal is not an arrow (%s)" uu____2819)
       in
    FStar_All.pipe_left (wrap_err "intro") uu____2740
  
let (intro_rec :
  unit ->
    (FStar_Syntax_Syntax.binder,FStar_Syntax_Syntax.binder)
      FStar_Pervasives_Native.tuple2 tac)
  =
  fun uu____2834  ->
    let uu____2841 = cur_goal ()  in
    bind uu____2841
      (fun goal  ->
         FStar_Util.print_string
           "WARNING (intro_rec): calling this is known to cause normalizer loops\n";
         FStar_Util.print_string
           "WARNING (intro_rec): proceed at your own risk...\n";
         (let uu____2858 =
            FStar_Syntax_Util.arrow_one goal.FStar_Tactics_Types.goal_ty  in
          match uu____2858 with
          | FStar_Pervasives_Native.Some (b,c) ->
              let uu____2877 =
                let uu____2878 = FStar_Syntax_Util.is_total_comp c  in
                Prims.op_Negation uu____2878  in
              if uu____2877
              then fail "Codomain is effectful"
              else
                (let bv =
                   FStar_Syntax_Syntax.gen_bv "__recf"
                     FStar_Pervasives_Native.None
                     goal.FStar_Tactics_Types.goal_ty
                    in
                 let bs =
                   let uu____2898 = FStar_Syntax_Syntax.mk_binder bv  in
                   [uu____2898; b]  in
                 let env' =
                   FStar_TypeChecker_Env.push_binders
                     goal.FStar_Tactics_Types.context bs
                    in
                 let uu____2916 =
                   let uu____2919 = comp_to_typ c  in
                   new_uvar "intro_rec" env' uu____2919  in
                 bind uu____2916
                   (fun u  ->
                      let lb =
                        let uu____2934 =
                          FStar_Syntax_Util.abs [b] u
                            FStar_Pervasives_Native.None
                           in
                        FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl bv)
                          [] goal.FStar_Tactics_Types.goal_ty
                          FStar_Parser_Const.effect_Tot_lid uu____2934 []
                          FStar_Range.dummyRange
                         in
                      let body = FStar_Syntax_Syntax.bv_to_name bv  in
                      let uu____2948 =
                        FStar_Syntax_Subst.close_let_rec [lb] body  in
                      match uu____2948 with
                      | (lbs,body1) ->
                          let tm =
                            FStar_Syntax_Syntax.mk
                              (FStar_Syntax_Syntax.Tm_let
                                 ((true, lbs), body1))
                              FStar_Pervasives_Native.None
                              (goal.FStar_Tactics_Types.witness).FStar_Syntax_Syntax.pos
                             in
                          let uu____2980 = trysolve goal tm  in
                          bind uu____2980
                            (fun bb  ->
                               if bb
                               then
                                 let uu____2996 =
                                   let uu____2999 =
                                     let uu___120_3000 = goal  in
                                     let uu____3001 = bnorm env' u  in
                                     let uu____3002 =
                                       let uu____3003 = comp_to_typ c  in
                                       bnorm env' uu____3003  in
                                     {
                                       FStar_Tactics_Types.context = env';
                                       FStar_Tactics_Types.witness =
                                         uu____3001;
                                       FStar_Tactics_Types.goal_ty =
                                         uu____3002;
                                       FStar_Tactics_Types.opts =
                                         (uu___120_3000.FStar_Tactics_Types.opts);
                                       FStar_Tactics_Types.is_guard =
                                         (uu___120_3000.FStar_Tactics_Types.is_guard)
                                     }  in
                                   replace_cur uu____2999  in
                                 bind uu____2996
                                   (fun uu____3010  ->
                                      let uu____3011 =
                                        let uu____3016 =
                                          FStar_Syntax_Syntax.mk_binder bv
                                           in
                                        (uu____3016, b)  in
                                      ret uu____3011)
                               else fail "intro_rec: unification failed")))
          | FStar_Pervasives_Native.None  ->
              let uu____3030 =
                tts goal.FStar_Tactics_Types.context
                  goal.FStar_Tactics_Types.goal_ty
                 in
              fail1 "intro_rec: goal is not an arrow (%s)" uu____3030))
  
let (norm : FStar_Syntax_Embeddings.norm_step Prims.list -> unit tac) =
  fun s  ->
    let uu____3048 = cur_goal ()  in
    bind uu____3048
      (fun goal  ->
         mlog
           (fun uu____3055  ->
              let uu____3056 =
                FStar_Syntax_Print.term_to_string
                  goal.FStar_Tactics_Types.witness
                 in
              FStar_Util.print1 "norm: witness = %s\n" uu____3056)
           (fun uu____3061  ->
              let steps =
                let uu____3065 = FStar_TypeChecker_Normalize.tr_norm_steps s
                   in
                FStar_List.append
                  [FStar_TypeChecker_Normalize.Reify;
                  FStar_TypeChecker_Normalize.UnfoldTac] uu____3065
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
                (let uu___121_3072 = goal  in
                 {
                   FStar_Tactics_Types.context =
                     (uu___121_3072.FStar_Tactics_Types.context);
                   FStar_Tactics_Types.witness = w;
                   FStar_Tactics_Types.goal_ty = t;
                   FStar_Tactics_Types.opts =
                     (uu___121_3072.FStar_Tactics_Types.opts);
                   FStar_Tactics_Types.is_guard =
                     (uu___121_3072.FStar_Tactics_Types.is_guard)
                 })))
  
let (norm_term_env :
  env ->
    FStar_Syntax_Embeddings.norm_step Prims.list ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac)
  =
  fun e  ->
    fun s  ->
      fun t  ->
        let uu____3096 =
          mlog
            (fun uu____3101  ->
               let uu____3102 = FStar_Syntax_Print.term_to_string t  in
               FStar_Util.print1 "norm_term: tm = %s\n" uu____3102)
            (fun uu____3104  ->
               bind get
                 (fun ps  ->
                    let opts =
                      match ps.FStar_Tactics_Types.goals with
                      | g::uu____3110 -> g.FStar_Tactics_Types.opts
                      | uu____3113 -> FStar_Options.peek ()  in
                    mlog
                      (fun uu____3118  ->
                         let uu____3119 =
                           tts ps.FStar_Tactics_Types.main_context t  in
                         FStar_Util.print1 "norm_term_env: t = %s\n"
                           uu____3119)
                      (fun uu____3122  ->
                         let uu____3123 = __tc e t  in
                         bind uu____3123
                           (fun uu____3144  ->
                              match uu____3144 with
                              | (t1,uu____3154,uu____3155) ->
                                  let steps =
                                    let uu____3159 =
                                      FStar_TypeChecker_Normalize.tr_norm_steps
                                        s
                                       in
                                    FStar_List.append
                                      [FStar_TypeChecker_Normalize.Reify;
                                      FStar_TypeChecker_Normalize.UnfoldTac]
                                      uu____3159
                                     in
                                  let t2 =
                                    normalize steps
                                      ps.FStar_Tactics_Types.main_context t1
                                     in
                                  ret t2))))
           in
        FStar_All.pipe_left (wrap_err "norm_term") uu____3096
  
let (refine_intro : unit -> unit tac) =
  fun uu____3173  ->
    let uu____3176 =
      let uu____3179 = cur_goal ()  in
      bind uu____3179
        (fun g  ->
           let uu____3186 =
             FStar_TypeChecker_Rel.base_and_refinement
               g.FStar_Tactics_Types.context g.FStar_Tactics_Types.goal_ty
              in
           match uu____3186 with
           | (uu____3199,FStar_Pervasives_Native.None ) ->
               fail "not a refinement"
           | (t,FStar_Pervasives_Native.Some (bv,phi)) ->
               let g1 =
                 let uu___122_3224 = g  in
                 {
                   FStar_Tactics_Types.context =
                     (uu___122_3224.FStar_Tactics_Types.context);
                   FStar_Tactics_Types.witness =
                     (uu___122_3224.FStar_Tactics_Types.witness);
                   FStar_Tactics_Types.goal_ty = t;
                   FStar_Tactics_Types.opts =
                     (uu___122_3224.FStar_Tactics_Types.opts);
                   FStar_Tactics_Types.is_guard =
                     (uu___122_3224.FStar_Tactics_Types.is_guard)
                 }  in
               let uu____3225 =
                 let uu____3230 =
                   let uu____3235 =
                     let uu____3236 = FStar_Syntax_Syntax.mk_binder bv  in
                     [uu____3236]  in
                   FStar_Syntax_Subst.open_term uu____3235 phi  in
                 match uu____3230 with
                 | (bvs,phi1) ->
                     let uu____3255 =
                       let uu____3256 = FStar_List.hd bvs  in
                       FStar_Pervasives_Native.fst uu____3256  in
                     (uu____3255, phi1)
                  in
               (match uu____3225 with
                | (bv1,phi1) ->
                    let uu____3269 =
                      let uu____3272 =
                        FStar_Syntax_Subst.subst
                          [FStar_Syntax_Syntax.NT
                             (bv1, (g.FStar_Tactics_Types.witness))] phi1
                         in
                      mk_irrelevant_goal "refine_intro refinement"
                        g.FStar_Tactics_Types.context uu____3272
                        g.FStar_Tactics_Types.opts
                       in
                    bind uu____3269
                      (fun g2  ->
                         bind __dismiss
                           (fun uu____3278  -> add_goals [g1; g2]))))
       in
    FStar_All.pipe_left (wrap_err "refine_intro") uu____3176
  
let (__exact_now : Prims.bool -> FStar_Syntax_Syntax.term -> unit tac) =
  fun set_expected_typ1  ->
    fun t  ->
      let uu____3297 = cur_goal ()  in
      bind uu____3297
        (fun goal  ->
           let env =
             if set_expected_typ1
             then
               FStar_TypeChecker_Env.set_expected_typ
                 goal.FStar_Tactics_Types.context
                 goal.FStar_Tactics_Types.goal_ty
             else goal.FStar_Tactics_Types.context  in
           let uu____3306 = __tc env t  in
           bind uu____3306
             (fun uu____3325  ->
                match uu____3325 with
                | (t1,typ,guard) ->
                    mlog
                      (fun uu____3340  ->
                         let uu____3341 =
                           tts goal.FStar_Tactics_Types.context typ  in
                         let uu____3342 =
                           FStar_TypeChecker_Rel.guard_to_string
                             goal.FStar_Tactics_Types.context guard
                            in
                         FStar_Util.print2
                           "__exact_now: got type %s\n__exact_now and guard %s\n"
                           uu____3341 uu____3342)
                      (fun uu____3345  ->
                         let uu____3346 =
                           proc_guard "__exact typing"
                             goal.FStar_Tactics_Types.context guard
                             goal.FStar_Tactics_Types.opts
                            in
                         bind uu____3346
                           (fun uu____3350  ->
                              mlog
                                (fun uu____3354  ->
                                   let uu____3355 =
                                     tts goal.FStar_Tactics_Types.context typ
                                      in
                                   let uu____3356 =
                                     tts goal.FStar_Tactics_Types.context
                                       goal.FStar_Tactics_Types.goal_ty
                                      in
                                   FStar_Util.print2
                                     "__exact_now: unifying %s and %s\n"
                                     uu____3355 uu____3356)
                                (fun uu____3359  ->
                                   let uu____3360 =
                                     do_unify
                                       goal.FStar_Tactics_Types.context typ
                                       goal.FStar_Tactics_Types.goal_ty
                                      in
                                   bind uu____3360
                                     (fun b  ->
                                        if b
                                        then solve goal t1
                                        else
                                          (let uu____3368 =
                                             tts
                                               goal.FStar_Tactics_Types.context
                                               t1
                                              in
                                           let uu____3369 =
                                             tts
                                               goal.FStar_Tactics_Types.context
                                               typ
                                              in
                                           let uu____3370 =
                                             tts
                                               goal.FStar_Tactics_Types.context
                                               goal.FStar_Tactics_Types.goal_ty
                                              in
                                           let uu____3371 =
                                             tts
                                               goal.FStar_Tactics_Types.context
                                               goal.FStar_Tactics_Types.witness
                                              in
                                           fail4
                                             "%s : %s does not exactly solve the goal %s (witness = %s)"
                                             uu____3368 uu____3369 uu____3370
                                             uu____3371)))))))
  
let (t_exact : Prims.bool -> FStar_Syntax_Syntax.term -> unit tac) =
  fun set_expected_typ1  ->
    fun tm  ->
      let uu____3386 =
        mlog
          (fun uu____3391  ->
             let uu____3392 = FStar_Syntax_Print.term_to_string tm  in
             FStar_Util.print1 "t_exact: tm = %s\n" uu____3392)
          (fun uu____3395  ->
             let uu____3396 =
               let uu____3403 = __exact_now set_expected_typ1 tm  in
               trytac' uu____3403  in
             bind uu____3396
               (fun uu___88_3412  ->
                  match uu___88_3412 with
                  | FStar_Util.Inr r -> ret ()
                  | FStar_Util.Inl e ->
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
                        (fun uu___87_3448  ->
                           match uu___87_3448 with
                           | FStar_Util.Inr r -> ret ()
                           | FStar_Util.Inl uu____3456 -> fail e)))
         in
      FStar_All.pipe_left (wrap_err "exact") uu____3386
  
let (uvar_free_in_goal :
  FStar_Syntax_Syntax.uvar -> FStar_Tactics_Types.goal -> Prims.bool) =
  fun u  ->
    fun g  ->
      if g.FStar_Tactics_Types.is_guard
      then false
      else
        (let free_uvars =
           let uu____3485 =
             let uu____3488 =
               FStar_Syntax_Free.uvars g.FStar_Tactics_Types.goal_ty  in
             FStar_Util.set_elements uu____3488  in
           FStar_List.map (fun u1  -> u1.FStar_Syntax_Syntax.ctx_uvar_head)
             uu____3485
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
          let uu____3568 = f x  in
          bind uu____3568
            (fun y  ->
               let uu____3576 = mapM f xs  in
               bind uu____3576 (fun ys  -> ret (y :: ys)))
  
exception NoUnif 
let (uu___is_NoUnif : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with | NoUnif  -> true | uu____3596 -> false
  
let rec (__apply :
  Prims.bool ->
    FStar_Syntax_Syntax.term -> FStar_Reflection_Data.typ -> unit tac)
  =
  fun uopt  ->
    fun tm  ->
      fun typ  ->
        let uu____3616 = cur_goal ()  in
        bind uu____3616
          (fun goal  ->
             mlog
               (fun uu____3623  ->
                  let uu____3624 = FStar_Syntax_Print.term_to_string tm  in
                  FStar_Util.print1 ">>> Calling __exact(%s)\n" uu____3624)
               (fun uu____3627  ->
                  let uu____3628 =
                    let uu____3633 =
                      let uu____3636 = t_exact false tm  in
                      with_policy FStar_Tactics_Types.Force uu____3636  in
                    trytac_exn uu____3633  in
                  bind uu____3628
                    (fun uu___89_3643  ->
                       match uu___89_3643 with
                       | FStar_Pervasives_Native.Some r -> ret ()
                       | FStar_Pervasives_Native.None  ->
                           mlog
                             (fun uu____3651  ->
                                let uu____3652 =
                                  FStar_Syntax_Print.term_to_string typ  in
                                FStar_Util.print1 ">>> typ = %s\n" uu____3652)
                             (fun uu____3655  ->
                                let uu____3656 =
                                  FStar_Syntax_Util.arrow_one typ  in
                                match uu____3656 with
                                | FStar_Pervasives_Native.None  ->
                                    FStar_Exn.raise NoUnif
                                | FStar_Pervasives_Native.Some ((bv,aq),c) ->
                                    mlog
                                      (fun uu____3680  ->
                                         let uu____3681 =
                                           FStar_Syntax_Print.binder_to_string
                                             (bv, aq)
                                            in
                                         FStar_Util.print1
                                           "__apply: pushing binder %s\n"
                                           uu____3681)
                                      (fun uu____3684  ->
                                         let uu____3685 =
                                           let uu____3686 =
                                             FStar_Syntax_Util.is_total_comp
                                               c
                                              in
                                           Prims.op_Negation uu____3686  in
                                         if uu____3685
                                         then
                                           fail "apply: not total codomain"
                                         else
                                           (let uu____3690 =
                                              new_uvar "apply"
                                                goal.FStar_Tactics_Types.context
                                                bv.FStar_Syntax_Syntax.sort
                                               in
                                            bind uu____3690
                                              (fun u  ->
                                                 let tm' =
                                                   FStar_Syntax_Syntax.mk_Tm_app
                                                     tm [(u, aq)]
                                                     FStar_Pervasives_Native.None
                                                     tm.FStar_Syntax_Syntax.pos
                                                    in
                                                 let typ' =
                                                   let uu____3716 =
                                                     comp_to_typ c  in
                                                   FStar_All.pipe_left
                                                     (FStar_Syntax_Subst.subst
                                                        [FStar_Syntax_Syntax.NT
                                                           (bv, u)])
                                                     uu____3716
                                                    in
                                                 let uu____3719 =
                                                   __apply uopt tm' typ'  in
                                                 bind uu____3719
                                                   (fun uu____3732  ->
                                                      let u1 =
                                                        bnorm
                                                          goal.FStar_Tactics_Types.context
                                                          u
                                                         in
                                                      let uu____3734 =
                                                        let uu____3735 =
                                                          let uu____3738 =
                                                            let uu____3739 =
                                                              FStar_Syntax_Util.head_and_args
                                                                u1
                                                               in
                                                            FStar_Pervasives_Native.fst
                                                              uu____3739
                                                             in
                                                          FStar_Syntax_Subst.compress
                                                            uu____3738
                                                           in
                                                        uu____3735.FStar_Syntax_Syntax.n
                                                         in
                                                      match uu____3734 with
                                                      | FStar_Syntax_Syntax.Tm_uvar
                                                          {
                                                            FStar_Syntax_Syntax.ctx_uvar_head
                                                              = uvar;
                                                            FStar_Syntax_Syntax.ctx_uvar_gamma
                                                              = uu____3767;
                                                            FStar_Syntax_Syntax.ctx_uvar_binders
                                                              = uu____3768;
                                                            FStar_Syntax_Syntax.ctx_uvar_typ
                                                              = uu____3769;
                                                            FStar_Syntax_Syntax.ctx_uvar_reason
                                                              = uu____3770;
                                                            FStar_Syntax_Syntax.ctx_uvar_should_check
                                                              = uu____3771;
                                                            FStar_Syntax_Syntax.ctx_uvar_range
                                                              = uu____3772;_}
                                                          ->
                                                          bind get
                                                            (fun ps  ->
                                                               let uu____3796
                                                                 =
                                                                 uopt &&
                                                                   (uvar_free
                                                                    uvar ps)
                                                                  in
                                                               if uu____3796
                                                               then ret ()
                                                               else
                                                                 (let uu____3800
                                                                    =
                                                                    let uu____3803
                                                                    =
                                                                    let uu___123_3804
                                                                    = goal
                                                                     in
                                                                    let uu____3805
                                                                    =
                                                                    bnorm
                                                                    goal.FStar_Tactics_Types.context
                                                                    u1  in
                                                                    let uu____3806
                                                                    =
                                                                    bnorm
                                                                    goal.FStar_Tactics_Types.context
                                                                    bv.FStar_Syntax_Syntax.sort
                                                                     in
                                                                    {
                                                                    FStar_Tactics_Types.context
                                                                    =
                                                                    (uu___123_3804.FStar_Tactics_Types.context);
                                                                    FStar_Tactics_Types.witness
                                                                    =
                                                                    uu____3805;
                                                                    FStar_Tactics_Types.goal_ty
                                                                    =
                                                                    uu____3806;
                                                                    FStar_Tactics_Types.opts
                                                                    =
                                                                    (uu___123_3804.FStar_Tactics_Types.opts);
                                                                    FStar_Tactics_Types.is_guard
                                                                    = false
                                                                    }  in
                                                                    [uu____3803]
                                                                     in
                                                                  add_goals
                                                                    uu____3800))
                                                      | t -> ret ()))))))))
  
let try_unif : 'a . 'a tac -> 'a tac -> 'a tac =
  fun t  ->
    fun t'  -> mk_tac (fun ps  -> try run t ps with | NoUnif  -> run t' ps)
  
let (apply : Prims.bool -> FStar_Syntax_Syntax.term -> unit tac) =
  fun uopt  ->
    fun tm  ->
      let uu____3861 =
        mlog
          (fun uu____3866  ->
             let uu____3867 = FStar_Syntax_Print.term_to_string tm  in
             FStar_Util.print1 "apply: tm = %s\n" uu____3867)
          (fun uu____3870  ->
             let uu____3871 = cur_goal ()  in
             bind uu____3871
               (fun goal  ->
                  let uu____3877 = __tc goal.FStar_Tactics_Types.context tm
                     in
                  bind uu____3877
                    (fun uu____3899  ->
                       match uu____3899 with
                       | (tm1,typ,guard) ->
                           let typ1 =
                             bnorm goal.FStar_Tactics_Types.context typ  in
                           let uu____3912 =
                             let uu____3915 =
                               let uu____3918 = __apply uopt tm1 typ1  in
                               bind uu____3918
                                 (fun uu____3922  ->
                                    proc_guard "apply guard"
                                      goal.FStar_Tactics_Types.context guard
                                      goal.FStar_Tactics_Types.opts)
                                in
                             focus uu____3915  in
                           let uu____3923 =
                             let uu____3926 =
                               tts goal.FStar_Tactics_Types.context tm1  in
                             let uu____3927 =
                               tts goal.FStar_Tactics_Types.context typ1  in
                             let uu____3928 =
                               tts goal.FStar_Tactics_Types.context
                                 goal.FStar_Tactics_Types.goal_ty
                                in
                             fail3
                               "Cannot instantiate %s (of type %s) to match goal (%s)"
                               uu____3926 uu____3927 uu____3928
                              in
                           try_unif uu____3912 uu____3923)))
         in
      FStar_All.pipe_left (wrap_err "apply") uu____3861
  
let (lemma_or_sq :
  FStar_Syntax_Syntax.comp ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun c  ->
    let ct = FStar_Syntax_Util.comp_to_comp_typ_nouniv c  in
    let uu____3951 =
      FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
        FStar_Parser_Const.effect_Lemma_lid
       in
    if uu____3951
    then
      let uu____3958 =
        match ct.FStar_Syntax_Syntax.effect_args with
        | pre::post::uu____3977 ->
            ((FStar_Pervasives_Native.fst pre),
              (FStar_Pervasives_Native.fst post))
        | uu____4018 -> failwith "apply_lemma: impossible: not a lemma"  in
      match uu____3958 with
      | (pre,post) ->
          let post1 =
            let uu____4054 =
              let uu____4063 =
                FStar_Syntax_Syntax.as_arg FStar_Syntax_Util.exp_unit  in
              [uu____4063]  in
            FStar_Syntax_Util.mk_app post uu____4054  in
          FStar_Pervasives_Native.Some (pre, post1)
    else
      (let uu____4087 =
         FStar_Syntax_Util.is_pure_effect ct.FStar_Syntax_Syntax.effect_name
          in
       if uu____4087
       then
         let uu____4094 =
           FStar_Syntax_Util.un_squash ct.FStar_Syntax_Syntax.result_typ  in
         FStar_Util.map_opt uu____4094
           (fun post  -> (FStar_Syntax_Util.t_true, post))
       else FStar_Pervasives_Native.None)
  
let (apply_lemma : FStar_Syntax_Syntax.term -> unit tac) =
  fun tm  ->
    let uu____4127 =
      let uu____4130 =
        mlog
          (fun uu____4135  ->
             let uu____4136 = FStar_Syntax_Print.term_to_string tm  in
             FStar_Util.print1 "apply_lemma: tm = %s\n" uu____4136)
          (fun uu____4140  ->
             let is_unit_t t =
               let uu____4147 =
                 let uu____4148 = FStar_Syntax_Subst.compress t  in
                 uu____4148.FStar_Syntax_Syntax.n  in
               match uu____4147 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.unit_lid
                   -> true
               | uu____4152 -> false  in
             let uu____4153 = cur_goal ()  in
             bind uu____4153
               (fun goal  ->
                  let uu____4159 = __tc goal.FStar_Tactics_Types.context tm
                     in
                  bind uu____4159
                    (fun uu____4182  ->
                       match uu____4182 with
                       | (tm1,t,guard) ->
                           let uu____4194 =
                             FStar_Syntax_Util.arrow_formals_comp t  in
                           (match uu____4194 with
                            | (bs,comp) ->
                                let uu____4221 = lemma_or_sq comp  in
                                (match uu____4221 with
                                 | FStar_Pervasives_Native.None  ->
                                     fail "not a lemma or squashed function"
                                 | FStar_Pervasives_Native.Some (pre,post) ->
                                     let uu____4240 =
                                       FStar_List.fold_left
                                         (fun uu____4282  ->
                                            fun uu____4283  ->
                                              match (uu____4282, uu____4283)
                                              with
                                              | ((uvs,guard1,subst1),(b,aq))
                                                  ->
                                                  let b_t =
                                                    FStar_Syntax_Subst.subst
                                                      subst1
                                                      b.FStar_Syntax_Syntax.sort
                                                     in
                                                  let uu____4374 =
                                                    is_unit_t b_t  in
                                                  if uu____4374
                                                  then
                                                    (((FStar_Syntax_Util.exp_unit,
                                                        aq) :: uvs), guard1,
                                                      ((FStar_Syntax_Syntax.NT
                                                          (b,
                                                            FStar_Syntax_Util.exp_unit))
                                                      :: subst1))
                                                  else
                                                    (let uu____4410 =
                                                       FStar_TypeChecker_Util.new_implicit_var
                                                         "apply_lemma"
                                                         (goal.FStar_Tactics_Types.goal_ty).FStar_Syntax_Syntax.pos
                                                         goal.FStar_Tactics_Types.context
                                                         b_t
                                                        in
                                                     match uu____4410 with
                                                     | (u,uu____4438,g_u) ->
                                                         let uu____4452 =
                                                           FStar_TypeChecker_Rel.conj_guard
                                                             guard1 g_u
                                                            in
                                                         (((u, aq) :: uvs),
                                                           uu____4452,
                                                           ((FStar_Syntax_Syntax.NT
                                                               (b, u)) ::
                                                           subst1))))
                                         ([], guard, []) bs
                                        in
                                     (match uu____4240 with
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
                                          let uu____4513 =
                                            let uu____4516 =
                                              FStar_Syntax_Util.mk_squash
                                                FStar_Syntax_Syntax.U_zero
                                                post1
                                               in
                                            do_unify
                                              goal.FStar_Tactics_Types.context
                                              uu____4516
                                              goal.FStar_Tactics_Types.goal_ty
                                             in
                                          bind uu____4513
                                            (fun b  ->
                                               if Prims.op_Negation b
                                               then
                                                 let uu____4524 =
                                                   tts
                                                     goal.FStar_Tactics_Types.context
                                                     tm1
                                                    in
                                                 let uu____4525 =
                                                   let uu____4526 =
                                                     FStar_Syntax_Util.mk_squash
                                                       FStar_Syntax_Syntax.U_zero
                                                       post1
                                                      in
                                                   tts
                                                     goal.FStar_Tactics_Types.context
                                                     uu____4526
                                                    in
                                                 let uu____4527 =
                                                   tts
                                                     goal.FStar_Tactics_Types.context
                                                     goal.FStar_Tactics_Types.goal_ty
                                                    in
                                                 fail3
                                                   "Cannot instantiate lemma %s (with postcondition: %s) to match goal (%s)"
                                                   uu____4524 uu____4525
                                                   uu____4527
                                               else
                                                 (let uu____4529 =
                                                    add_implicits
                                                      implicits.FStar_TypeChecker_Env.implicits
                                                     in
                                                  bind uu____4529
                                                    (fun uu____4534  ->
                                                       let uu____4535 =
                                                         solve goal
                                                           FStar_Syntax_Util.exp_unit
                                                          in
                                                       bind uu____4535
                                                         (fun uu____4543  ->
                                                            let is_free_uvar
                                                              uv t1 =
                                                              let free_uvars
                                                                =
                                                                let uu____4568
                                                                  =
                                                                  let uu____4571
                                                                    =
                                                                    FStar_Syntax_Free.uvars
                                                                    t1  in
                                                                  FStar_Util.set_elements
                                                                    uu____4571
                                                                   in
                                                                FStar_List.map
                                                                  (fun x  ->
                                                                    x.FStar_Syntax_Syntax.ctx_uvar_head)
                                                                  uu____4568
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
                                                              let uu____4620
                                                                =
                                                                FStar_Syntax_Util.head_and_args
                                                                  t1
                                                                 in
                                                              match uu____4620
                                                              with
                                                              | (hd1,uu____4636)
                                                                  ->
                                                                  (match 
                                                                    hd1.FStar_Syntax_Syntax.n
                                                                   with
                                                                   | 
                                                                   FStar_Syntax_Syntax.Tm_uvar
                                                                    uv ->
                                                                    appears
                                                                    uv.FStar_Syntax_Syntax.ctx_uvar_head
                                                                    goals
                                                                   | 
                                                                   uu____4658
                                                                    -> false)
                                                               in
                                                            let uu____4659 =
                                                              FStar_All.pipe_right
                                                                implicits.FStar_TypeChecker_Env.implicits
                                                                (mapM
                                                                   (fun
                                                                    uu____4727
                                                                     ->
                                                                    match uu____4727
                                                                    with
                                                                    | 
                                                                    (_msg,term,ctx_uvar,_range,uu____4752)
                                                                    ->
                                                                    let uu____4753
                                                                    =
                                                                    FStar_Syntax_Util.head_and_args
                                                                    term  in
                                                                    (match uu____4753
                                                                    with
                                                                    | 
                                                                    (hd1,uu____4779)
                                                                    ->
                                                                    let env =
                                                                    let uu___126_4801
                                                                    =
                                                                    goal.FStar_Tactics_Types.context
                                                                     in
                                                                    {
                                                                    FStar_TypeChecker_Env.solver
                                                                    =
                                                                    (uu___126_4801.FStar_TypeChecker_Env.solver);
                                                                    FStar_TypeChecker_Env.range
                                                                    =
                                                                    (uu___126_4801.FStar_TypeChecker_Env.range);
                                                                    FStar_TypeChecker_Env.curmodule
                                                                    =
                                                                    (uu___126_4801.FStar_TypeChecker_Env.curmodule);
                                                                    FStar_TypeChecker_Env.gamma
                                                                    =
                                                                    (ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_gamma);
                                                                    FStar_TypeChecker_Env.gamma_sig
                                                                    =
                                                                    (uu___126_4801.FStar_TypeChecker_Env.gamma_sig);
                                                                    FStar_TypeChecker_Env.gamma_cache
                                                                    =
                                                                    (uu___126_4801.FStar_TypeChecker_Env.gamma_cache);
                                                                    FStar_TypeChecker_Env.modules
                                                                    =
                                                                    (uu___126_4801.FStar_TypeChecker_Env.modules);
                                                                    FStar_TypeChecker_Env.expected_typ
                                                                    =
                                                                    (uu___126_4801.FStar_TypeChecker_Env.expected_typ);
                                                                    FStar_TypeChecker_Env.sigtab
                                                                    =
                                                                    (uu___126_4801.FStar_TypeChecker_Env.sigtab);
                                                                    FStar_TypeChecker_Env.is_pattern
                                                                    =
                                                                    (uu___126_4801.FStar_TypeChecker_Env.is_pattern);
                                                                    FStar_TypeChecker_Env.instantiate_imp
                                                                    =
                                                                    (uu___126_4801.FStar_TypeChecker_Env.instantiate_imp);
                                                                    FStar_TypeChecker_Env.effects
                                                                    =
                                                                    (uu___126_4801.FStar_TypeChecker_Env.effects);
                                                                    FStar_TypeChecker_Env.generalize
                                                                    =
                                                                    (uu___126_4801.FStar_TypeChecker_Env.generalize);
                                                                    FStar_TypeChecker_Env.letrecs
                                                                    =
                                                                    (uu___126_4801.FStar_TypeChecker_Env.letrecs);
                                                                    FStar_TypeChecker_Env.top_level
                                                                    =
                                                                    (uu___126_4801.FStar_TypeChecker_Env.top_level);
                                                                    FStar_TypeChecker_Env.check_uvars
                                                                    =
                                                                    (uu___126_4801.FStar_TypeChecker_Env.check_uvars);
                                                                    FStar_TypeChecker_Env.use_eq
                                                                    =
                                                                    (uu___126_4801.FStar_TypeChecker_Env.use_eq);
                                                                    FStar_TypeChecker_Env.is_iface
                                                                    =
                                                                    (uu___126_4801.FStar_TypeChecker_Env.is_iface);
                                                                    FStar_TypeChecker_Env.admit
                                                                    =
                                                                    (uu___126_4801.FStar_TypeChecker_Env.admit);
                                                                    FStar_TypeChecker_Env.lax
                                                                    =
                                                                    (uu___126_4801.FStar_TypeChecker_Env.lax);
                                                                    FStar_TypeChecker_Env.lax_universes
                                                                    =
                                                                    (uu___126_4801.FStar_TypeChecker_Env.lax_universes);
                                                                    FStar_TypeChecker_Env.failhard
                                                                    =
                                                                    (uu___126_4801.FStar_TypeChecker_Env.failhard);
                                                                    FStar_TypeChecker_Env.nosynth
                                                                    =
                                                                    (uu___126_4801.FStar_TypeChecker_Env.nosynth);
                                                                    FStar_TypeChecker_Env.tc_term
                                                                    =
                                                                    (uu___126_4801.FStar_TypeChecker_Env.tc_term);
                                                                    FStar_TypeChecker_Env.type_of
                                                                    =
                                                                    (uu___126_4801.FStar_TypeChecker_Env.type_of);
                                                                    FStar_TypeChecker_Env.universe_of
                                                                    =
                                                                    (uu___126_4801.FStar_TypeChecker_Env.universe_of);
                                                                    FStar_TypeChecker_Env.check_type_of
                                                                    =
                                                                    (uu___126_4801.FStar_TypeChecker_Env.check_type_of);
                                                                    FStar_TypeChecker_Env.use_bv_sorts
                                                                    =
                                                                    (uu___126_4801.FStar_TypeChecker_Env.use_bv_sorts);
                                                                    FStar_TypeChecker_Env.qtbl_name_and_index
                                                                    =
                                                                    (uu___126_4801.FStar_TypeChecker_Env.qtbl_name_and_index);
                                                                    FStar_TypeChecker_Env.normalized_eff_names
                                                                    =
                                                                    (uu___126_4801.FStar_TypeChecker_Env.normalized_eff_names);
                                                                    FStar_TypeChecker_Env.proof_ns
                                                                    =
                                                                    (uu___126_4801.FStar_TypeChecker_Env.proof_ns);
                                                                    FStar_TypeChecker_Env.synth_hook
                                                                    =
                                                                    (uu___126_4801.FStar_TypeChecker_Env.synth_hook);
                                                                    FStar_TypeChecker_Env.splice
                                                                    =
                                                                    (uu___126_4801.FStar_TypeChecker_Env.splice);
                                                                    FStar_TypeChecker_Env.is_native_tactic
                                                                    =
                                                                    (uu___126_4801.FStar_TypeChecker_Env.is_native_tactic);
                                                                    FStar_TypeChecker_Env.identifier_info
                                                                    =
                                                                    (uu___126_4801.FStar_TypeChecker_Env.identifier_info);
                                                                    FStar_TypeChecker_Env.tc_hooks
                                                                    =
                                                                    (uu___126_4801.FStar_TypeChecker_Env.tc_hooks);
                                                                    FStar_TypeChecker_Env.dsenv
                                                                    =
                                                                    (uu___126_4801.FStar_TypeChecker_Env.dsenv);
                                                                    FStar_TypeChecker_Env.dep_graph
                                                                    =
                                                                    (uu___126_4801.FStar_TypeChecker_Env.dep_graph)
                                                                    }  in
                                                                    let uu____4802
                                                                    =
                                                                    let uu____4803
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    hd1  in
                                                                    uu____4803.FStar_Syntax_Syntax.n
                                                                     in
                                                                    (match uu____4802
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Tm_uvar
                                                                    uu____4816
                                                                    ->
                                                                    let uu____4817
                                                                    =
                                                                    let uu____4826
                                                                    =
                                                                    let uu____4829
                                                                    =
                                                                    let uu___127_4830
                                                                    = goal
                                                                     in
                                                                    let uu____4831
                                                                    =
                                                                    bnorm env
                                                                    term  in
                                                                    let uu____4832
                                                                    =
                                                                    bnorm env
                                                                    ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_typ
                                                                     in
                                                                    {
                                                                    FStar_Tactics_Types.context
                                                                    = env;
                                                                    FStar_Tactics_Types.witness
                                                                    =
                                                                    uu____4831;
                                                                    FStar_Tactics_Types.goal_ty
                                                                    =
                                                                    uu____4832;
                                                                    FStar_Tactics_Types.opts
                                                                    =
                                                                    (uu___127_4830.FStar_Tactics_Types.opts);
                                                                    FStar_Tactics_Types.is_guard
                                                                    =
                                                                    (uu___127_4830.FStar_Tactics_Types.is_guard)
                                                                    }  in
                                                                    [uu____4829]
                                                                     in
                                                                    (uu____4826,
                                                                    [])  in
                                                                    ret
                                                                    uu____4817
                                                                    | 
                                                                    uu____4845
                                                                    ->
                                                                    let g_typ
                                                                    =
                                                                    let uu____4847
                                                                    =
                                                                    FStar_Options.__temp_fast_implicits
                                                                    ()  in
                                                                    if
                                                                    uu____4847
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
                                                                    let uu____4850
                                                                    =
                                                                    let uu____4857
                                                                    =
                                                                    FStar_TypeChecker_Env.set_expected_typ
                                                                    env
                                                                    ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_typ
                                                                     in
                                                                    env.FStar_TypeChecker_Env.type_of
                                                                    uu____4857
                                                                    term1  in
                                                                    match uu____4850
                                                                    with
                                                                    | 
                                                                    (uu____4858,uu____4859,g_typ)
                                                                    -> g_typ)
                                                                     in
                                                                    let uu____4861
                                                                    =
                                                                    goal_from_guard
                                                                    "apply_lemma solved arg"
                                                                    goal.FStar_Tactics_Types.context
                                                                    g_typ
                                                                    goal.FStar_Tactics_Types.opts
                                                                     in
                                                                    bind
                                                                    uu____4861
                                                                    (fun
                                                                    uu___90_4877
                                                                     ->
                                                                    match uu___90_4877
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
                                                            bind uu____4659
                                                              (fun goals_  ->
                                                                 let sub_goals
                                                                   =
                                                                   let uu____4945
                                                                    =
                                                                    FStar_List.map
                                                                    FStar_Pervasives_Native.fst
                                                                    goals_
                                                                     in
                                                                   FStar_List.flatten
                                                                    uu____4945
                                                                    in
                                                                 let smt_goals
                                                                   =
                                                                   let uu____4967
                                                                    =
                                                                    FStar_List.map
                                                                    FStar_Pervasives_Native.snd
                                                                    goals_
                                                                     in
                                                                   FStar_List.flatten
                                                                    uu____4967
                                                                    in
                                                                 let rec filter'
                                                                   f xs =
                                                                   match xs
                                                                   with
                                                                   | 
                                                                   [] -> []
                                                                   | 
                                                                   x::xs1 ->
                                                                    let uu____5028
                                                                    = f x xs1
                                                                     in
                                                                    if
                                                                    uu____5028
                                                                    then
                                                                    let uu____5031
                                                                    =
                                                                    filter' f
                                                                    xs1  in x
                                                                    ::
                                                                    uu____5031
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
                                                                    let uu____5045
                                                                    =
                                                                    checkone
                                                                    g.FStar_Tactics_Types.witness
                                                                    goals  in
                                                                    Prims.op_Negation
                                                                    uu____5045)
                                                                    sub_goals
                                                                    in
                                                                 let uu____5046
                                                                   =
                                                                   proc_guard
                                                                    "apply_lemma guard"
                                                                    goal.FStar_Tactics_Types.context
                                                                    guard
                                                                    goal.FStar_Tactics_Types.opts
                                                                    in
                                                                 bind
                                                                   uu____5046
                                                                   (fun
                                                                    uu____5051
                                                                     ->
                                                                    let uu____5052
                                                                    =
                                                                    let uu____5055
                                                                    =
                                                                    let uu____5056
                                                                    =
                                                                    let uu____5057
                                                                    =
                                                                    FStar_Syntax_Util.mk_squash
                                                                    FStar_Syntax_Syntax.U_zero
                                                                    pre1  in
                                                                    istrivial
                                                                    goal.FStar_Tactics_Types.context
                                                                    uu____5057
                                                                     in
                                                                    Prims.op_Negation
                                                                    uu____5056
                                                                     in
                                                                    if
                                                                    uu____5055
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
                                                                    uu____5052
                                                                    (fun
                                                                    uu____5063
                                                                     ->
                                                                    let uu____5064
                                                                    =
                                                                    add_smt_goals
                                                                    smt_goals
                                                                     in
                                                                    bind
                                                                    uu____5064
                                                                    (fun
                                                                    uu____5068
                                                                     ->
                                                                    add_goals
                                                                    sub_goals1))))))))))))))
         in
      focus uu____4130  in
    FStar_All.pipe_left (wrap_err "apply_lemma") uu____4127
  
let (destruct_eq' :
  FStar_Reflection_Data.typ ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun typ  ->
    let uu____5090 = FStar_Syntax_Util.destruct_typ_as_formula typ  in
    match uu____5090 with
    | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn
        (l,uu____5100::(e1,uu____5102)::(e2,uu____5104)::[])) when
        FStar_Ident.lid_equals l FStar_Parser_Const.eq2_lid ->
        FStar_Pervasives_Native.Some (e1, e2)
    | uu____5147 -> FStar_Pervasives_Native.None
  
let (destruct_eq :
  FStar_Reflection_Data.typ ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun typ  ->
    let uu____5171 = destruct_eq' typ  in
    match uu____5171 with
    | FStar_Pervasives_Native.Some t -> FStar_Pervasives_Native.Some t
    | FStar_Pervasives_Native.None  ->
        let uu____5201 = FStar_Syntax_Util.un_squash typ  in
        (match uu____5201 with
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
        let uu____5263 = FStar_TypeChecker_Env.pop_bv e1  in
        match uu____5263 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (bv',e') ->
            if FStar_Syntax_Syntax.bv_eq bvar bv'
            then FStar_Pervasives_Native.Some (e', [])
            else
              (let uu____5311 = aux e'  in
               FStar_Util.map_opt uu____5311
                 (fun uu____5335  ->
                    match uu____5335 with | (e'',bvs) -> (e'', (bv' :: bvs))))
         in
      let uu____5356 = aux e  in
      FStar_Util.map_opt uu____5356
        (fun uu____5380  ->
           match uu____5380 with | (e',bvs) -> (e', (FStar_List.rev bvs)))
  
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
          let uu____5447 = split_env b1 g.FStar_Tactics_Types.context  in
          FStar_Util.map_opt uu____5447
            (fun uu____5471  ->
               match uu____5471 with
               | (e0,bvs) ->
                   let s1 bv =
                     let uu___128_5490 = bv  in
                     let uu____5491 =
                       FStar_Syntax_Subst.subst s bv.FStar_Syntax_Syntax.sort
                        in
                     {
                       FStar_Syntax_Syntax.ppname =
                         (uu___128_5490.FStar_Syntax_Syntax.ppname);
                       FStar_Syntax_Syntax.index =
                         (uu___128_5490.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort = uu____5491
                     }  in
                   let bvs1 = FStar_List.map s1 bvs  in
                   let c = push_bvs e0 (b2 :: bvs1)  in
                   let w =
                     FStar_Syntax_Subst.subst s g.FStar_Tactics_Types.witness
                      in
                   let t =
                     FStar_Syntax_Subst.subst s g.FStar_Tactics_Types.goal_ty
                      in
                   let uu___129_5500 = g  in
                   {
                     FStar_Tactics_Types.context = c;
                     FStar_Tactics_Types.witness = w;
                     FStar_Tactics_Types.goal_ty = t;
                     FStar_Tactics_Types.opts =
                       (uu___129_5500.FStar_Tactics_Types.opts);
                     FStar_Tactics_Types.is_guard =
                       (uu___129_5500.FStar_Tactics_Types.is_guard)
                   })
  
let (rewrite : FStar_Syntax_Syntax.binder -> unit tac) =
  fun h  ->
    let uu____5510 = cur_goal ()  in
    bind uu____5510
      (fun goal  ->
         let uu____5518 = h  in
         match uu____5518 with
         | (bv,uu____5522) ->
             mlog
               (fun uu____5526  ->
                  let uu____5527 = FStar_Syntax_Print.bv_to_string bv  in
                  let uu____5528 =
                    tts goal.FStar_Tactics_Types.context
                      bv.FStar_Syntax_Syntax.sort
                     in
                  FStar_Util.print2 "+++Rewrite %s : %s\n" uu____5527
                    uu____5528)
               (fun uu____5531  ->
                  let uu____5532 =
                    split_env bv goal.FStar_Tactics_Types.context  in
                  match uu____5532 with
                  | FStar_Pervasives_Native.None  ->
                      fail "rewrite: binder not found in environment"
                  | FStar_Pervasives_Native.Some (e0,bvs) ->
                      let uu____5561 =
                        destruct_eq bv.FStar_Syntax_Syntax.sort  in
                      (match uu____5561 with
                       | FStar_Pervasives_Native.Some (x,e) ->
                           let uu____5576 =
                             let uu____5577 = FStar_Syntax_Subst.compress x
                                in
                             uu____5577.FStar_Syntax_Syntax.n  in
                           (match uu____5576 with
                            | FStar_Syntax_Syntax.Tm_name x1 ->
                                let s = [FStar_Syntax_Syntax.NT (x1, e)]  in
                                let s1 bv1 =
                                  let uu___130_5594 = bv1  in
                                  let uu____5595 =
                                    FStar_Syntax_Subst.subst s
                                      bv1.FStar_Syntax_Syntax.sort
                                     in
                                  {
                                    FStar_Syntax_Syntax.ppname =
                                      (uu___130_5594.FStar_Syntax_Syntax.ppname);
                                    FStar_Syntax_Syntax.index =
                                      (uu___130_5594.FStar_Syntax_Syntax.index);
                                    FStar_Syntax_Syntax.sort = uu____5595
                                  }  in
                                let bvs1 = FStar_List.map s1 bvs  in
                                let uu____5601 =
                                  let uu___131_5602 = goal  in
                                  let uu____5603 = push_bvs e0 (bv :: bvs1)
                                     in
                                  let uu____5604 =
                                    FStar_Syntax_Subst.subst s
                                      goal.FStar_Tactics_Types.witness
                                     in
                                  let uu____5605 =
                                    FStar_Syntax_Subst.subst s
                                      goal.FStar_Tactics_Types.goal_ty
                                     in
                                  {
                                    FStar_Tactics_Types.context = uu____5603;
                                    FStar_Tactics_Types.witness = uu____5604;
                                    FStar_Tactics_Types.goal_ty = uu____5605;
                                    FStar_Tactics_Types.opts =
                                      (uu___131_5602.FStar_Tactics_Types.opts);
                                    FStar_Tactics_Types.is_guard =
                                      (uu___131_5602.FStar_Tactics_Types.is_guard)
                                  }  in
                                replace_cur uu____5601
                            | uu____5606 ->
                                fail
                                  "rewrite: Not an equality hypothesis with a variable on the LHS")
                       | uu____5607 ->
                           fail "rewrite: Not an equality hypothesis")))
  
let (rename_to : FStar_Syntax_Syntax.binder -> Prims.string -> unit tac) =
  fun b  ->
    fun s  ->
      let uu____5628 = cur_goal ()  in
      bind uu____5628
        (fun goal  ->
           let uu____5639 = b  in
           match uu____5639 with
           | (bv,uu____5643) ->
               let bv' =
                 let uu____5645 =
                   let uu___132_5646 = bv  in
                   let uu____5647 =
                     FStar_Ident.mk_ident
                       (s,
                         ((bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))
                      in
                   {
                     FStar_Syntax_Syntax.ppname = uu____5647;
                     FStar_Syntax_Syntax.index =
                       (uu___132_5646.FStar_Syntax_Syntax.index);
                     FStar_Syntax_Syntax.sort =
                       (uu___132_5646.FStar_Syntax_Syntax.sort)
                   }  in
                 FStar_Syntax_Syntax.freshen_bv uu____5645  in
               let s1 =
                 let uu____5651 =
                   let uu____5652 =
                     let uu____5659 = FStar_Syntax_Syntax.bv_to_name bv'  in
                     (bv, uu____5659)  in
                   FStar_Syntax_Syntax.NT uu____5652  in
                 [uu____5651]  in
               let uu____5664 = subst_goal bv bv' s1 goal  in
               (match uu____5664 with
                | FStar_Pervasives_Native.None  ->
                    fail "rename_to: binder not found in environment"
                | FStar_Pervasives_Native.Some goal1 -> replace_cur goal1))
  
let (binder_retype : FStar_Syntax_Syntax.binder -> unit tac) =
  fun b  ->
    let uu____5679 = cur_goal ()  in
    bind uu____5679
      (fun goal  ->
         let uu____5688 = b  in
         match uu____5688 with
         | (bv,uu____5692) ->
             let uu____5693 = split_env bv goal.FStar_Tactics_Types.context
                in
             (match uu____5693 with
              | FStar_Pervasives_Native.None  ->
                  fail "binder_retype: binder is not present in environment"
              | FStar_Pervasives_Native.Some (e0,bvs) ->
                  let uu____5722 = FStar_Syntax_Util.type_u ()  in
                  (match uu____5722 with
                   | (ty,u) ->
                       let uu____5731 = new_uvar "binder_retype" e0 ty  in
                       bind uu____5731
                         (fun t'  ->
                            let bv'' =
                              let uu___133_5741 = bv  in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___133_5741.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___133_5741.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = t'
                              }  in
                            let s =
                              let uu____5745 =
                                let uu____5746 =
                                  let uu____5753 =
                                    FStar_Syntax_Syntax.bv_to_name bv''  in
                                  (bv, uu____5753)  in
                                FStar_Syntax_Syntax.NT uu____5746  in
                              [uu____5745]  in
                            let bvs1 =
                              FStar_List.map
                                (fun b1  ->
                                   let uu___134_5765 = b1  in
                                   let uu____5766 =
                                     FStar_Syntax_Subst.subst s
                                       b1.FStar_Syntax_Syntax.sort
                                      in
                                   {
                                     FStar_Syntax_Syntax.ppname =
                                       (uu___134_5765.FStar_Syntax_Syntax.ppname);
                                     FStar_Syntax_Syntax.index =
                                       (uu___134_5765.FStar_Syntax_Syntax.index);
                                     FStar_Syntax_Syntax.sort = uu____5766
                                   }) bvs
                               in
                            let env' = push_bvs e0 (bv'' :: bvs1)  in
                            bind __dismiss
                              (fun uu____5772  ->
                                 let uu____5773 =
                                   let uu____5776 =
                                     let uu____5779 =
                                       let uu___135_5780 = goal  in
                                       let uu____5781 =
                                         FStar_Syntax_Subst.subst s
                                           goal.FStar_Tactics_Types.witness
                                          in
                                       let uu____5782 =
                                         FStar_Syntax_Subst.subst s
                                           goal.FStar_Tactics_Types.goal_ty
                                          in
                                       {
                                         FStar_Tactics_Types.context = env';
                                         FStar_Tactics_Types.witness =
                                           uu____5781;
                                         FStar_Tactics_Types.goal_ty =
                                           uu____5782;
                                         FStar_Tactics_Types.opts =
                                           (uu___135_5780.FStar_Tactics_Types.opts);
                                         FStar_Tactics_Types.is_guard =
                                           (uu___135_5780.FStar_Tactics_Types.is_guard)
                                       }  in
                                     [uu____5779]  in
                                   add_goals uu____5776  in
                                 bind uu____5773
                                   (fun uu____5785  ->
                                      let uu____5786 =
                                        FStar_Syntax_Util.mk_eq2
                                          (FStar_Syntax_Syntax.U_succ u) ty
                                          bv.FStar_Syntax_Syntax.sort t'
                                         in
                                      add_irrelevant_goal
                                        "binder_retype equation" e0
                                        uu____5786
                                        goal.FStar_Tactics_Types.opts))))))
  
let (norm_binder_type :
  FStar_Syntax_Embeddings.norm_step Prims.list ->
    FStar_Syntax_Syntax.binder -> unit tac)
  =
  fun s  ->
    fun b  ->
      let uu____5805 = cur_goal ()  in
      bind uu____5805
        (fun goal  ->
           let uu____5814 = b  in
           match uu____5814 with
           | (bv,uu____5818) ->
               let uu____5819 = split_env bv goal.FStar_Tactics_Types.context
                  in
               (match uu____5819 with
                | FStar_Pervasives_Native.None  ->
                    fail
                      "binder_retype: binder is not present in environment"
                | FStar_Pervasives_Native.Some (e0,bvs) ->
                    let steps =
                      let uu____5851 =
                        FStar_TypeChecker_Normalize.tr_norm_steps s  in
                      FStar_List.append
                        [FStar_TypeChecker_Normalize.Reify;
                        FStar_TypeChecker_Normalize.UnfoldTac] uu____5851
                       in
                    let sort' =
                      normalize steps e0 bv.FStar_Syntax_Syntax.sort  in
                    let bv' =
                      let uu___136_5856 = bv  in
                      {
                        FStar_Syntax_Syntax.ppname =
                          (uu___136_5856.FStar_Syntax_Syntax.ppname);
                        FStar_Syntax_Syntax.index =
                          (uu___136_5856.FStar_Syntax_Syntax.index);
                        FStar_Syntax_Syntax.sort = sort'
                      }  in
                    let env' = push_bvs e0 (bv' :: bvs)  in
                    replace_cur
                      (let uu___137_5860 = goal  in
                       {
                         FStar_Tactics_Types.context = env';
                         FStar_Tactics_Types.witness =
                           (uu___137_5860.FStar_Tactics_Types.witness);
                         FStar_Tactics_Types.goal_ty =
                           (uu___137_5860.FStar_Tactics_Types.goal_ty);
                         FStar_Tactics_Types.opts =
                           (uu___137_5860.FStar_Tactics_Types.opts);
                         FStar_Tactics_Types.is_guard =
                           (uu___137_5860.FStar_Tactics_Types.is_guard)
                       })))
  
let (revert : unit -> unit tac) =
  fun uu____5867  ->
    let uu____5870 = cur_goal ()  in
    bind uu____5870
      (fun goal  ->
         let uu____5876 =
           FStar_TypeChecker_Env.pop_bv goal.FStar_Tactics_Types.context  in
         match uu____5876 with
         | FStar_Pervasives_Native.None  ->
             fail "Cannot revert; empty context"
         | FStar_Pervasives_Native.Some (x,env') ->
             let typ' =
               let uu____5898 =
                 FStar_Syntax_Syntax.mk_Total
                   goal.FStar_Tactics_Types.goal_ty
                  in
               FStar_Syntax_Util.arrow [(x, FStar_Pervasives_Native.None)]
                 uu____5898
                in
             let w' =
               FStar_Syntax_Util.abs [(x, FStar_Pervasives_Native.None)]
                 goal.FStar_Tactics_Types.witness
                 FStar_Pervasives_Native.None
                in
             replace_cur
               (let uu___138_5922 = goal  in
                {
                  FStar_Tactics_Types.context = env';
                  FStar_Tactics_Types.witness = w';
                  FStar_Tactics_Types.goal_ty = typ';
                  FStar_Tactics_Types.opts =
                    (uu___138_5922.FStar_Tactics_Types.opts);
                  FStar_Tactics_Types.is_guard =
                    (uu___138_5922.FStar_Tactics_Types.is_guard)
                }))
  
let (free_in :
  FStar_Syntax_Syntax.bv -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun bv  ->
    fun t  ->
      let uu____5933 = FStar_Syntax_Free.names t  in
      FStar_Util.set_mem bv uu____5933
  
let rec (clear : FStar_Syntax_Syntax.binder -> unit tac) =
  fun b  ->
    let bv = FStar_Pervasives_Native.fst b  in
    let uu____5946 = cur_goal ()  in
    bind uu____5946
      (fun goal  ->
         mlog
           (fun uu____5954  ->
              let uu____5955 = FStar_Syntax_Print.binder_to_string b  in
              let uu____5956 =
                let uu____5957 =
                  let uu____5958 =
                    FStar_TypeChecker_Env.all_binders
                      goal.FStar_Tactics_Types.context
                     in
                  FStar_All.pipe_right uu____5958 FStar_List.length  in
                FStar_All.pipe_right uu____5957 FStar_Util.string_of_int  in
              FStar_Util.print2 "Clear of (%s), env has %s binders\n"
                uu____5955 uu____5956)
           (fun uu____5977  ->
              let uu____5978 = split_env bv goal.FStar_Tactics_Types.context
                 in
              match uu____5978 with
              | FStar_Pervasives_Native.None  ->
                  fail "Cannot clear; binder not in environment"
              | FStar_Pervasives_Native.Some (e',bvs) ->
                  let rec check1 bvs1 =
                    match bvs1 with
                    | [] -> ret ()
                    | bv'::bvs2 ->
                        let uu____6025 =
                          free_in bv bv'.FStar_Syntax_Syntax.sort  in
                        if uu____6025
                        then
                          let uu____6028 =
                            let uu____6029 =
                              FStar_Syntax_Print.bv_to_string bv'  in
                            FStar_Util.format1
                              "Cannot clear; binder present in the type of %s"
                              uu____6029
                             in
                          fail uu____6028
                        else check1 bvs2
                     in
                  let uu____6031 =
                    free_in bv goal.FStar_Tactics_Types.goal_ty  in
                  if uu____6031
                  then fail "Cannot clear; binder present in goal"
                  else
                    (let uu____6035 = check1 bvs  in
                     bind uu____6035
                       (fun uu____6041  ->
                          let env' = push_bvs e' bvs  in
                          let uu____6043 =
                            new_uvar "clear.witness" env'
                              goal.FStar_Tactics_Types.goal_ty
                             in
                          bind uu____6043
                            (fun ut  ->
                               let uu____6049 =
                                 do_unify goal.FStar_Tactics_Types.context
                                   goal.FStar_Tactics_Types.witness ut
                                  in
                               bind uu____6049
                                 (fun b1  ->
                                    if b1
                                    then
                                      replace_cur
                                        (let uu___139_6058 = goal  in
                                         {
                                           FStar_Tactics_Types.context = env';
                                           FStar_Tactics_Types.witness = ut;
                                           FStar_Tactics_Types.goal_ty =
                                             (uu___139_6058.FStar_Tactics_Types.goal_ty);
                                           FStar_Tactics_Types.opts =
                                             (uu___139_6058.FStar_Tactics_Types.opts);
                                           FStar_Tactics_Types.is_guard =
                                             (uu___139_6058.FStar_Tactics_Types.is_guard)
                                         })
                                    else
                                      fail
                                        "Cannot clear; binder appears in witness"))))))
  
let (clear_top : unit -> unit tac) =
  fun uu____6066  ->
    let uu____6069 = cur_goal ()  in
    bind uu____6069
      (fun goal  ->
         let uu____6075 =
           FStar_TypeChecker_Env.pop_bv goal.FStar_Tactics_Types.context  in
         match uu____6075 with
         | FStar_Pervasives_Native.None  ->
             fail "Cannot clear; empty context"
         | FStar_Pervasives_Native.Some (x,uu____6089) ->
             let uu____6094 = FStar_Syntax_Syntax.mk_binder x  in
             clear uu____6094)
  
let (prune : Prims.string -> unit tac) =
  fun s  ->
    let uu____6104 = cur_goal ()  in
    bind uu____6104
      (fun g  ->
         let ctx = g.FStar_Tactics_Types.context  in
         let ctx' =
           let uu____6114 = FStar_Ident.path_of_text s  in
           FStar_TypeChecker_Env.rem_proof_ns ctx uu____6114  in
         let g' =
           let uu___140_6116 = g  in
           {
             FStar_Tactics_Types.context = ctx';
             FStar_Tactics_Types.witness =
               (uu___140_6116.FStar_Tactics_Types.witness);
             FStar_Tactics_Types.goal_ty =
               (uu___140_6116.FStar_Tactics_Types.goal_ty);
             FStar_Tactics_Types.opts =
               (uu___140_6116.FStar_Tactics_Types.opts);
             FStar_Tactics_Types.is_guard =
               (uu___140_6116.FStar_Tactics_Types.is_guard)
           }  in
         bind __dismiss (fun uu____6118  -> add_goals [g']))
  
let (addns : Prims.string -> unit tac) =
  fun s  ->
    let uu____6128 = cur_goal ()  in
    bind uu____6128
      (fun g  ->
         let ctx = g.FStar_Tactics_Types.context  in
         let ctx' =
           let uu____6138 = FStar_Ident.path_of_text s  in
           FStar_TypeChecker_Env.add_proof_ns ctx uu____6138  in
         let g' =
           let uu___141_6140 = g  in
           {
             FStar_Tactics_Types.context = ctx';
             FStar_Tactics_Types.witness =
               (uu___141_6140.FStar_Tactics_Types.witness);
             FStar_Tactics_Types.goal_ty =
               (uu___141_6140.FStar_Tactics_Types.goal_ty);
             FStar_Tactics_Types.opts =
               (uu___141_6140.FStar_Tactics_Types.opts);
             FStar_Tactics_Types.is_guard =
               (uu___141_6140.FStar_Tactics_Types.is_guard)
           }  in
         bind __dismiss (fun uu____6142  -> add_goals [g']))
  
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
            let uu____6182 = FStar_Syntax_Subst.compress t  in
            uu____6182.FStar_Syntax_Syntax.n  in
          let uu____6185 =
            if d = FStar_Tactics_Types.TopDown
            then
              f env
                (let uu___145_6191 = t  in
                 {
                   FStar_Syntax_Syntax.n = tn;
                   FStar_Syntax_Syntax.pos =
                     (uu___145_6191.FStar_Syntax_Syntax.pos);
                   FStar_Syntax_Syntax.vars =
                     (uu___145_6191.FStar_Syntax_Syntax.vars)
                 })
            else ret t  in
          bind uu____6185
            (fun t1  ->
               let ff = tac_fold_env d f env  in
               let tn1 =
                 let uu____6207 =
                   let uu____6208 = FStar_Syntax_Subst.compress t1  in
                   uu____6208.FStar_Syntax_Syntax.n  in
                 match uu____6207 with
                 | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
                     let uu____6235 = ff hd1  in
                     bind uu____6235
                       (fun hd2  ->
                          let fa uu____6257 =
                            match uu____6257 with
                            | (a,q) ->
                                let uu____6270 = ff a  in
                                bind uu____6270 (fun a1  -> ret (a1, q))
                             in
                          let uu____6283 = mapM fa args  in
                          bind uu____6283
                            (fun args1  ->
                               ret (FStar_Syntax_Syntax.Tm_app (hd2, args1))))
                 | FStar_Syntax_Syntax.Tm_abs (bs,t2,k) ->
                     let uu____6349 = FStar_Syntax_Subst.open_term bs t2  in
                     (match uu____6349 with
                      | (bs1,t') ->
                          let uu____6358 =
                            let uu____6361 =
                              FStar_TypeChecker_Env.push_binders env bs1  in
                            tac_fold_env d f uu____6361 t'  in
                          bind uu____6358
                            (fun t''  ->
                               let uu____6365 =
                                 let uu____6366 =
                                   let uu____6383 =
                                     FStar_Syntax_Subst.close_binders bs1  in
                                   let uu____6390 =
                                     FStar_Syntax_Subst.close bs1 t''  in
                                   (uu____6383, uu____6390, k)  in
                                 FStar_Syntax_Syntax.Tm_abs uu____6366  in
                               ret uu____6365))
                 | FStar_Syntax_Syntax.Tm_arrow (bs,k) -> ret tn
                 | FStar_Syntax_Syntax.Tm_match (hd1,brs) ->
                     let uu____6459 = ff hd1  in
                     bind uu____6459
                       (fun hd2  ->
                          let ffb br =
                            let uu____6474 =
                              FStar_Syntax_Subst.open_branch br  in
                            match uu____6474 with
                            | (pat,w,e) ->
                                let bvs = FStar_Syntax_Syntax.pat_bvs pat  in
                                let ff1 =
                                  let uu____6506 =
                                    FStar_TypeChecker_Env.push_bvs env bvs
                                     in
                                  tac_fold_env d f uu____6506  in
                                let uu____6507 = ff1 e  in
                                bind uu____6507
                                  (fun e1  ->
                                     let br1 =
                                       FStar_Syntax_Subst.close_branch
                                         (pat, w, e1)
                                        in
                                     ret br1)
                             in
                          let uu____6522 = mapM ffb brs  in
                          bind uu____6522
                            (fun brs1  ->
                               ret (FStar_Syntax_Syntax.Tm_match (hd2, brs1))))
                 | FStar_Syntax_Syntax.Tm_let
                     ((false
                       ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl bv;
                          FStar_Syntax_Syntax.lbunivs = uu____6566;
                          FStar_Syntax_Syntax.lbtyp = uu____6567;
                          FStar_Syntax_Syntax.lbeff = uu____6568;
                          FStar_Syntax_Syntax.lbdef = def;
                          FStar_Syntax_Syntax.lbattrs = uu____6570;
                          FStar_Syntax_Syntax.lbpos = uu____6571;_}::[]),e)
                     ->
                     let lb =
                       let uu____6596 =
                         let uu____6597 = FStar_Syntax_Subst.compress t1  in
                         uu____6597.FStar_Syntax_Syntax.n  in
                       match uu____6596 with
                       | FStar_Syntax_Syntax.Tm_let
                           ((false ,lb::[]),uu____6601) -> lb
                       | uu____6614 -> failwith "impossible"  in
                     let fflb lb1 =
                       let uu____6623 = ff lb1.FStar_Syntax_Syntax.lbdef  in
                       bind uu____6623
                         (fun def1  ->
                            ret
                              (let uu___142_6629 = lb1  in
                               {
                                 FStar_Syntax_Syntax.lbname =
                                   (uu___142_6629.FStar_Syntax_Syntax.lbname);
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___142_6629.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp =
                                   (uu___142_6629.FStar_Syntax_Syntax.lbtyp);
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___142_6629.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def1;
                                 FStar_Syntax_Syntax.lbattrs =
                                   (uu___142_6629.FStar_Syntax_Syntax.lbattrs);
                                 FStar_Syntax_Syntax.lbpos =
                                   (uu___142_6629.FStar_Syntax_Syntax.lbpos)
                               }))
                        in
                     let uu____6630 = fflb lb  in
                     bind uu____6630
                       (fun lb1  ->
                          let uu____6640 =
                            let uu____6645 =
                              let uu____6646 =
                                FStar_Syntax_Syntax.mk_binder bv  in
                              [uu____6646]  in
                            FStar_Syntax_Subst.open_term uu____6645 e  in
                          match uu____6640 with
                          | (bs,e1) ->
                              let ff1 =
                                let uu____6670 =
                                  FStar_TypeChecker_Env.push_binders env bs
                                   in
                                tac_fold_env d f uu____6670  in
                              let uu____6671 = ff1 e1  in
                              bind uu____6671
                                (fun e2  ->
                                   let e3 = FStar_Syntax_Subst.close bs e2
                                      in
                                   ret
                                     (FStar_Syntax_Syntax.Tm_let
                                        ((false, [lb1]), e3))))
                 | FStar_Syntax_Syntax.Tm_let ((true ,lbs),e) ->
                     let fflb lb =
                       let uu____6712 = ff lb.FStar_Syntax_Syntax.lbdef  in
                       bind uu____6712
                         (fun def  ->
                            ret
                              (let uu___143_6718 = lb  in
                               {
                                 FStar_Syntax_Syntax.lbname =
                                   (uu___143_6718.FStar_Syntax_Syntax.lbname);
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___143_6718.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp =
                                   (uu___143_6718.FStar_Syntax_Syntax.lbtyp);
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___143_6718.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def;
                                 FStar_Syntax_Syntax.lbattrs =
                                   (uu___143_6718.FStar_Syntax_Syntax.lbattrs);
                                 FStar_Syntax_Syntax.lbpos =
                                   (uu___143_6718.FStar_Syntax_Syntax.lbpos)
                               }))
                        in
                     let uu____6719 = FStar_Syntax_Subst.open_let_rec lbs e
                        in
                     (match uu____6719 with
                      | (lbs1,e1) ->
                          let uu____6734 = mapM fflb lbs1  in
                          bind uu____6734
                            (fun lbs2  ->
                               let uu____6746 = ff e1  in
                               bind uu____6746
                                 (fun e2  ->
                                    let uu____6754 =
                                      FStar_Syntax_Subst.close_let_rec lbs2
                                        e2
                                       in
                                    match uu____6754 with
                                    | (lbs3,e3) ->
                                        ret
                                          (FStar_Syntax_Syntax.Tm_let
                                             ((true, lbs3), e3)))))
                 | FStar_Syntax_Syntax.Tm_ascribed (t2,asc,eff) ->
                     let uu____6822 = ff t2  in
                     bind uu____6822
                       (fun t3  ->
                          ret
                            (FStar_Syntax_Syntax.Tm_ascribed (t3, asc, eff)))
                 | FStar_Syntax_Syntax.Tm_meta (t2,m) ->
                     let uu____6853 = ff t2  in
                     bind uu____6853
                       (fun t3  -> ret (FStar_Syntax_Syntax.Tm_meta (t3, m)))
                 | uu____6860 -> ret tn  in
               bind tn1
                 (fun tn2  ->
                    let t' =
                      let uu___144_6867 = t1  in
                      {
                        FStar_Syntax_Syntax.n = tn2;
                        FStar_Syntax_Syntax.pos =
                          (uu___144_6867.FStar_Syntax_Syntax.pos);
                        FStar_Syntax_Syntax.vars =
                          (uu___144_6867.FStar_Syntax_Syntax.vars)
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
            let uu____6904 = FStar_TypeChecker_TcTerm.tc_term env t  in
            match uu____6904 with
            | (t1,lcomp,g) ->
                let uu____6916 =
                  (let uu____6919 =
                     FStar_Syntax_Util.is_pure_or_ghost_lcomp lcomp  in
                   Prims.op_Negation uu____6919) ||
                    (let uu____6921 = FStar_TypeChecker_Rel.is_trivial g  in
                     Prims.op_Negation uu____6921)
                   in
                if uu____6916
                then ret t1
                else
                  (let rewrite_eq =
                     let typ = lcomp.FStar_Syntax_Syntax.res_typ  in
                     let uu____6931 = new_uvar "pointwise_rec" env typ  in
                     bind uu____6931
                       (fun ut  ->
                          log ps
                            (fun uu____6942  ->
                               let uu____6943 =
                                 FStar_Syntax_Print.term_to_string t1  in
                               let uu____6944 =
                                 FStar_Syntax_Print.term_to_string ut  in
                               FStar_Util.print2
                                 "Pointwise_rec: making equality\n\t%s ==\n\t%s\n"
                                 uu____6943 uu____6944);
                          (let uu____6945 =
                             let uu____6948 =
                               let uu____6949 =
                                 FStar_TypeChecker_TcTerm.universe_of env typ
                                  in
                               FStar_Syntax_Util.mk_eq2 uu____6949 typ t1 ut
                                in
                             add_irrelevant_goal "pointwise_rec equation" env
                               uu____6948 opts
                              in
                           bind uu____6945
                             (fun uu____6952  ->
                                let uu____6953 =
                                  bind tau
                                    (fun uu____6959  ->
                                       let ut1 =
                                         FStar_TypeChecker_Normalize.reduce_uvar_solutions
                                           env ut
                                          in
                                       log ps
                                         (fun uu____6965  ->
                                            let uu____6966 =
                                              FStar_Syntax_Print.term_to_string
                                                t1
                                               in
                                            let uu____6967 =
                                              FStar_Syntax_Print.term_to_string
                                                ut1
                                               in
                                            FStar_Util.print2
                                              "Pointwise_rec: succeeded rewriting\n\t%s to\n\t%s\n"
                                              uu____6966 uu____6967);
                                       ret ut1)
                                   in
                                focus uu____6953)))
                      in
                   let uu____6968 = trytac' rewrite_eq  in
                   bind uu____6968
                     (fun x  ->
                        match x with
                        | FStar_Util.Inl "SKIP" -> ret t1
                        | FStar_Util.Inl e -> fail e
                        | FStar_Util.Inr x1 -> ret x1))
  
type ctrl = FStar_BigInt.t[@@deriving show]
let (keepGoing : ctrl) = FStar_BigInt.zero 
let (proceedToNextSubtree : FStar_BigInt.bigint) = FStar_BigInt.one 
let (globalStop : FStar_BigInt.bigint) =
  FStar_BigInt.succ_big_int FStar_BigInt.one 
type rewrite_result = Prims.bool[@@deriving show]
let (skipThisTerm : Prims.bool) = false 
let (rewroteThisTerm : Prims.bool) = true 
type 'a ctrl_tac = ('a,ctrl) FStar_Pervasives_Native.tuple2 tac[@@deriving
                                                                 show]
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
          let uu____7166 = FStar_Syntax_Subst.compress t  in
          maybe_continue ctrl uu____7166
            (fun t1  ->
               let uu____7174 =
                 f env
                   (let uu___148_7183 = t1  in
                    {
                      FStar_Syntax_Syntax.n = (t1.FStar_Syntax_Syntax.n);
                      FStar_Syntax_Syntax.pos =
                        (uu___148_7183.FStar_Syntax_Syntax.pos);
                      FStar_Syntax_Syntax.vars =
                        (uu___148_7183.FStar_Syntax_Syntax.vars)
                    })
                  in
               bind uu____7174
                 (fun uu____7199  ->
                    match uu____7199 with
                    | (t2,ctrl1) ->
                        maybe_continue ctrl1 t2
                          (fun t3  ->
                             let uu____7222 =
                               let uu____7223 =
                                 FStar_Syntax_Subst.compress t3  in
                               uu____7223.FStar_Syntax_Syntax.n  in
                             match uu____7222 with
                             | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
                                 let uu____7256 =
                                   ctrl_tac_fold f env ctrl1 hd1  in
                                 bind uu____7256
                                   (fun uu____7281  ->
                                      match uu____7281 with
                                      | (hd2,ctrl2) ->
                                          let ctrl3 = keep_going ctrl2  in
                                          let uu____7297 =
                                            ctrl_tac_fold_args f env ctrl3
                                              args
                                             in
                                          bind uu____7297
                                            (fun uu____7324  ->
                                               match uu____7324 with
                                               | (args1,ctrl4) ->
                                                   ret
                                                     ((let uu___146_7354 = t3
                                                          in
                                                       {
                                                         FStar_Syntax_Syntax.n
                                                           =
                                                           (FStar_Syntax_Syntax.Tm_app
                                                              (hd2, args1));
                                                         FStar_Syntax_Syntax.pos
                                                           =
                                                           (uu___146_7354.FStar_Syntax_Syntax.pos);
                                                         FStar_Syntax_Syntax.vars
                                                           =
                                                           (uu___146_7354.FStar_Syntax_Syntax.vars)
                                                       }), ctrl4)))
                             | FStar_Syntax_Syntax.Tm_abs (bs,t4,k) ->
                                 let uu____7390 =
                                   FStar_Syntax_Subst.open_term bs t4  in
                                 (match uu____7390 with
                                  | (bs1,t') ->
                                      let uu____7405 =
                                        let uu____7412 =
                                          FStar_TypeChecker_Env.push_binders
                                            env bs1
                                           in
                                        ctrl_tac_fold f uu____7412 ctrl1 t'
                                         in
                                      bind uu____7405
                                        (fun uu____7430  ->
                                           match uu____7430 with
                                           | (t'',ctrl2) ->
                                               let uu____7445 =
                                                 let uu____7452 =
                                                   let uu___147_7455 = t4  in
                                                   let uu____7458 =
                                                     let uu____7459 =
                                                       let uu____7476 =
                                                         FStar_Syntax_Subst.close_binders
                                                           bs1
                                                          in
                                                       let uu____7483 =
                                                         FStar_Syntax_Subst.close
                                                           bs1 t''
                                                          in
                                                       (uu____7476,
                                                         uu____7483, k)
                                                        in
                                                     FStar_Syntax_Syntax.Tm_abs
                                                       uu____7459
                                                      in
                                                   {
                                                     FStar_Syntax_Syntax.n =
                                                       uu____7458;
                                                     FStar_Syntax_Syntax.pos
                                                       =
                                                       (uu___147_7455.FStar_Syntax_Syntax.pos);
                                                     FStar_Syntax_Syntax.vars
                                                       =
                                                       (uu___147_7455.FStar_Syntax_Syntax.vars)
                                                   }  in
                                                 (uu____7452, ctrl2)  in
                                               ret uu____7445))
                             | FStar_Syntax_Syntax.Tm_arrow (bs,k) ->
                                 ret (t3, ctrl1)
                             | uu____7530 -> ret (t3, ctrl1))))

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
              let uu____7573 = ctrl_tac_fold f env ctrl t  in
              bind uu____7573
                (fun uu____7597  ->
                   match uu____7597 with
                   | (t1,ctrl1) ->
                       let uu____7612 = ctrl_tac_fold_args f env ctrl1 ts1
                          in
                       bind uu____7612
                         (fun uu____7639  ->
                            match uu____7639 with
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
              let uu____7721 =
                let uu____7728 =
                  add_irrelevant_goal "dummy" env FStar_Syntax_Util.t_true
                    opts
                   in
                bind uu____7728
                  (fun uu____7737  ->
                     let uu____7738 = ctrl t1  in
                     bind uu____7738
                       (fun res  ->
                          let uu____7761 = trivial ()  in
                          bind uu____7761 (fun uu____7769  -> ret res)))
                 in
              bind uu____7721
                (fun uu____7785  ->
                   match uu____7785 with
                   | (should_rewrite,ctrl1) ->
                       if Prims.op_Negation should_rewrite
                       then ret (t1, ctrl1)
                       else
                         (let uu____7809 =
                            FStar_TypeChecker_TcTerm.tc_term env t1  in
                          match uu____7809 with
                          | (t2,lcomp,g) ->
                              let uu____7825 =
                                (let uu____7828 =
                                   FStar_Syntax_Util.is_pure_or_ghost_lcomp
                                     lcomp
                                    in
                                 Prims.op_Negation uu____7828) ||
                                  (let uu____7830 =
                                     FStar_TypeChecker_Rel.is_trivial g  in
                                   Prims.op_Negation uu____7830)
                                 in
                              if uu____7825
                              then ret (t2, globalStop)
                              else
                                (let typ = lcomp.FStar_Syntax_Syntax.res_typ
                                    in
                                 let uu____7845 =
                                   new_uvar "pointwise_rec" env typ  in
                                 bind uu____7845
                                   (fun ut  ->
                                      log ps
                                        (fun uu____7860  ->
                                           let uu____7861 =
                                             FStar_Syntax_Print.term_to_string
                                               t2
                                              in
                                           let uu____7862 =
                                             FStar_Syntax_Print.term_to_string
                                               ut
                                              in
                                           FStar_Util.print2
                                             "Pointwise_rec: making equality\n\t%s ==\n\t%s\n"
                                             uu____7861 uu____7862);
                                      (let uu____7863 =
                                         let uu____7866 =
                                           let uu____7867 =
                                             FStar_TypeChecker_TcTerm.universe_of
                                               env typ
                                              in
                                           FStar_Syntax_Util.mk_eq2
                                             uu____7867 typ t2 ut
                                            in
                                         add_irrelevant_goal
                                           "rewrite_rec equation" env
                                           uu____7866 opts
                                          in
                                       bind uu____7863
                                         (fun uu____7874  ->
                                            let uu____7875 =
                                              bind rewriter
                                                (fun uu____7889  ->
                                                   let ut1 =
                                                     FStar_TypeChecker_Normalize.reduce_uvar_solutions
                                                       env ut
                                                      in
                                                   log ps
                                                     (fun uu____7895  ->
                                                        let uu____7896 =
                                                          FStar_Syntax_Print.term_to_string
                                                            t2
                                                           in
                                                        let uu____7897 =
                                                          FStar_Syntax_Print.term_to_string
                                                            ut1
                                                           in
                                                        FStar_Util.print2
                                                          "rewrite_rec: succeeded rewriting\n\t%s to\n\t%s\n"
                                                          uu____7896
                                                          uu____7897);
                                                   ret (ut1, ctrl1))
                                               in
                                            focus uu____7875))))))
  
let (topdown_rewrite :
  (FStar_Syntax_Syntax.term ->
     (Prims.bool,FStar_BigInt.t) FStar_Pervasives_Native.tuple2 tac)
    -> unit tac -> unit tac)
  =
  fun ctrl  ->
    fun rewriter  ->
      bind get
        (fun ps  ->
           let uu____7945 =
             match ps.FStar_Tactics_Types.goals with
             | g::gs -> (g, gs)
             | [] -> failwith "Pointwise: no goals"  in
           match uu____7945 with
           | (g,gs) ->
               let gt1 = g.FStar_Tactics_Types.goal_ty  in
               (log ps
                  (fun uu____7982  ->
                     let uu____7983 = FStar_Syntax_Print.term_to_string gt1
                        in
                     FStar_Util.print1 "Topdown_rewrite starting with %s\n"
                       uu____7983);
                bind dismiss_all
                  (fun uu____7986  ->
                     let uu____7987 =
                       ctrl_tac_fold
                         (rewrite_rec ps ctrl rewriter
                            g.FStar_Tactics_Types.opts)
                         g.FStar_Tactics_Types.context keepGoing gt1
                        in
                     bind uu____7987
                       (fun uu____8005  ->
                          match uu____8005 with
                          | (gt',uu____8013) ->
                              (log ps
                                 (fun uu____8017  ->
                                    let uu____8018 =
                                      FStar_Syntax_Print.term_to_string gt'
                                       in
                                    FStar_Util.print1
                                      "Topdown_rewrite seems to have succeded with %s\n"
                                      uu____8018);
                               (let uu____8019 = push_goals gs  in
                                bind uu____8019
                                  (fun uu____8023  ->
                                     add_goals
                                       [(let uu___149_8025 = g  in
                                         {
                                           FStar_Tactics_Types.context =
                                             (uu___149_8025.FStar_Tactics_Types.context);
                                           FStar_Tactics_Types.witness =
                                             (uu___149_8025.FStar_Tactics_Types.witness);
                                           FStar_Tactics_Types.goal_ty = gt';
                                           FStar_Tactics_Types.opts =
                                             (uu___149_8025.FStar_Tactics_Types.opts);
                                           FStar_Tactics_Types.is_guard =
                                             (uu___149_8025.FStar_Tactics_Types.is_guard)
                                         })])))))))
  
let (pointwise : FStar_Tactics_Types.direction -> unit tac -> unit tac) =
  fun d  ->
    fun tau  ->
      bind get
        (fun ps  ->
           let uu____8051 =
             match ps.FStar_Tactics_Types.goals with
             | g::gs -> (g, gs)
             | [] -> failwith "Pointwise: no goals"  in
           match uu____8051 with
           | (g,gs) ->
               let gt1 = g.FStar_Tactics_Types.goal_ty  in
               (log ps
                  (fun uu____8088  ->
                     let uu____8089 = FStar_Syntax_Print.term_to_string gt1
                        in
                     FStar_Util.print1 "Pointwise starting with %s\n"
                       uu____8089);
                bind dismiss_all
                  (fun uu____8092  ->
                     let uu____8093 =
                       tac_fold_env d
                         (pointwise_rec ps tau g.FStar_Tactics_Types.opts)
                         g.FStar_Tactics_Types.context gt1
                        in
                     bind uu____8093
                       (fun gt'  ->
                          log ps
                            (fun uu____8103  ->
                               let uu____8104 =
                                 FStar_Syntax_Print.term_to_string gt'  in
                               FStar_Util.print1
                                 "Pointwise seems to have succeded with %s\n"
                                 uu____8104);
                          (let uu____8105 = push_goals gs  in
                           bind uu____8105
                             (fun uu____8109  ->
                                add_goals
                                  [(let uu___150_8111 = g  in
                                    {
                                      FStar_Tactics_Types.context =
                                        (uu___150_8111.FStar_Tactics_Types.context);
                                      FStar_Tactics_Types.witness =
                                        (uu___150_8111.FStar_Tactics_Types.witness);
                                      FStar_Tactics_Types.goal_ty = gt';
                                      FStar_Tactics_Types.opts =
                                        (uu___150_8111.FStar_Tactics_Types.opts);
                                      FStar_Tactics_Types.is_guard =
                                        (uu___150_8111.FStar_Tactics_Types.is_guard)
                                    })]))))))
  
let (trefl : unit -> unit tac) =
  fun uu____8118  ->
    let uu____8121 = cur_goal ()  in
    bind uu____8121
      (fun g  ->
         let uu____8139 =
           FStar_Syntax_Util.un_squash g.FStar_Tactics_Types.goal_ty  in
         match uu____8139 with
         | FStar_Pervasives_Native.Some t ->
             let uu____8151 = FStar_Syntax_Util.head_and_args' t  in
             (match uu____8151 with
              | (hd1,args) ->
                  let uu____8184 =
                    let uu____8195 =
                      let uu____8196 = FStar_Syntax_Util.un_uinst hd1  in
                      uu____8196.FStar_Syntax_Syntax.n  in
                    (uu____8195, args)  in
                  (match uu____8184 with
                   | (FStar_Syntax_Syntax.Tm_fvar
                      fv,uu____8208::(l,uu____8210)::(r,uu____8212)::[]) when
                       FStar_Syntax_Syntax.fv_eq_lid fv
                         FStar_Parser_Const.eq2_lid
                       ->
                       let uu____8239 =
                         do_unify g.FStar_Tactics_Types.context l r  in
                       bind uu____8239
                         (fun b  ->
                            if Prims.op_Negation b
                            then
                              let uu____8248 =
                                tts g.FStar_Tactics_Types.context l  in
                              let uu____8249 =
                                tts g.FStar_Tactics_Types.context r  in
                              fail2
                                "trefl: not a trivial equality (%s vs %s)"
                                uu____8248 uu____8249
                            else solve g FStar_Syntax_Util.exp_unit)
                   | (hd2,uu____8252) ->
                       let uu____8265 = tts g.FStar_Tactics_Types.context t
                          in
                       fail1 "trefl: not an equality (%s)" uu____8265))
         | FStar_Pervasives_Native.None  -> fail "not an irrelevant goal")
  
let (dup : unit -> unit tac) =
  fun uu____8274  ->
    let uu____8277 = cur_goal ()  in
    bind uu____8277
      (fun g  ->
         let uu____8283 =
           new_uvar "dup" g.FStar_Tactics_Types.context
             g.FStar_Tactics_Types.goal_ty
            in
         bind uu____8283
           (fun u  ->
              let g' =
                let uu___151_8290 = g  in
                {
                  FStar_Tactics_Types.context =
                    (uu___151_8290.FStar_Tactics_Types.context);
                  FStar_Tactics_Types.witness = u;
                  FStar_Tactics_Types.goal_ty =
                    (uu___151_8290.FStar_Tactics_Types.goal_ty);
                  FStar_Tactics_Types.opts =
                    (uu___151_8290.FStar_Tactics_Types.opts);
                  FStar_Tactics_Types.is_guard =
                    (uu___151_8290.FStar_Tactics_Types.is_guard)
                }  in
              bind __dismiss
                (fun uu____8293  ->
                   let uu____8294 =
                     let uu____8297 =
                       let uu____8298 =
                         FStar_TypeChecker_TcTerm.universe_of
                           g.FStar_Tactics_Types.context
                           g.FStar_Tactics_Types.goal_ty
                          in
                       FStar_Syntax_Util.mk_eq2 uu____8298
                         g.FStar_Tactics_Types.goal_ty u
                         g.FStar_Tactics_Types.witness
                        in
                     add_irrelevant_goal "dup equation"
                       g.FStar_Tactics_Types.context uu____8297
                       g.FStar_Tactics_Types.opts
                      in
                   bind uu____8294
                     (fun uu____8301  ->
                        let uu____8302 = add_goals [g']  in
                        bind uu____8302 (fun uu____8306  -> ret ())))))
  
let (flip : unit -> unit tac) =
  fun uu____8313  ->
    bind get
      (fun ps  ->
         match ps.FStar_Tactics_Types.goals with
         | g1::g2::gs ->
             set
               (let uu___152_8330 = ps  in
                {
                  FStar_Tactics_Types.main_context =
                    (uu___152_8330.FStar_Tactics_Types.main_context);
                  FStar_Tactics_Types.main_goal =
                    (uu___152_8330.FStar_Tactics_Types.main_goal);
                  FStar_Tactics_Types.all_implicits =
                    (uu___152_8330.FStar_Tactics_Types.all_implicits);
                  FStar_Tactics_Types.goals = (g2 :: g1 :: gs);
                  FStar_Tactics_Types.smt_goals =
                    (uu___152_8330.FStar_Tactics_Types.smt_goals);
                  FStar_Tactics_Types.depth =
                    (uu___152_8330.FStar_Tactics_Types.depth);
                  FStar_Tactics_Types.__dump =
                    (uu___152_8330.FStar_Tactics_Types.__dump);
                  FStar_Tactics_Types.psc =
                    (uu___152_8330.FStar_Tactics_Types.psc);
                  FStar_Tactics_Types.entry_range =
                    (uu___152_8330.FStar_Tactics_Types.entry_range);
                  FStar_Tactics_Types.guard_policy =
                    (uu___152_8330.FStar_Tactics_Types.guard_policy);
                  FStar_Tactics_Types.freshness =
                    (uu___152_8330.FStar_Tactics_Types.freshness)
                })
         | uu____8331 -> fail "flip: less than 2 goals")
  
let (later : unit -> unit tac) =
  fun uu____8340  ->
    bind get
      (fun ps  ->
         match ps.FStar_Tactics_Types.goals with
         | [] -> ret ()
         | g::gs ->
             set
               (let uu___153_8353 = ps  in
                {
                  FStar_Tactics_Types.main_context =
                    (uu___153_8353.FStar_Tactics_Types.main_context);
                  FStar_Tactics_Types.main_goal =
                    (uu___153_8353.FStar_Tactics_Types.main_goal);
                  FStar_Tactics_Types.all_implicits =
                    (uu___153_8353.FStar_Tactics_Types.all_implicits);
                  FStar_Tactics_Types.goals = (FStar_List.append gs [g]);
                  FStar_Tactics_Types.smt_goals =
                    (uu___153_8353.FStar_Tactics_Types.smt_goals);
                  FStar_Tactics_Types.depth =
                    (uu___153_8353.FStar_Tactics_Types.depth);
                  FStar_Tactics_Types.__dump =
                    (uu___153_8353.FStar_Tactics_Types.__dump);
                  FStar_Tactics_Types.psc =
                    (uu___153_8353.FStar_Tactics_Types.psc);
                  FStar_Tactics_Types.entry_range =
                    (uu___153_8353.FStar_Tactics_Types.entry_range);
                  FStar_Tactics_Types.guard_policy =
                    (uu___153_8353.FStar_Tactics_Types.guard_policy);
                  FStar_Tactics_Types.freshness =
                    (uu___153_8353.FStar_Tactics_Types.freshness)
                }))
  
let (qed : unit -> unit tac) =
  fun uu____8360  ->
    bind get
      (fun ps  ->
         match ps.FStar_Tactics_Types.goals with
         | [] -> ret ()
         | uu____8367 -> fail "Not done!")
  
let (cases :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 tac)
  =
  fun t  ->
    let uu____8387 =
      let uu____8394 = cur_goal ()  in
      bind uu____8394
        (fun g  ->
           let uu____8404 = __tc g.FStar_Tactics_Types.context t  in
           bind uu____8404
             (fun uu____8440  ->
                match uu____8440 with
                | (t1,typ,guard) ->
                    let uu____8456 = FStar_Syntax_Util.head_and_args typ  in
                    (match uu____8456 with
                     | (hd1,args) ->
                         let uu____8499 =
                           let uu____8512 =
                             let uu____8513 = FStar_Syntax_Util.un_uinst hd1
                                in
                             uu____8513.FStar_Syntax_Syntax.n  in
                           (uu____8512, args)  in
                         (match uu____8499 with
                          | (FStar_Syntax_Syntax.Tm_fvar
                             fv,(p,uu____8532)::(q,uu____8534)::[]) when
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
                                let uu___154_8572 = g  in
                                let uu____8573 =
                                  FStar_TypeChecker_Env.push_bv
                                    g.FStar_Tactics_Types.context v_p
                                   in
                                {
                                  FStar_Tactics_Types.context = uu____8573;
                                  FStar_Tactics_Types.witness =
                                    (uu___154_8572.FStar_Tactics_Types.witness);
                                  FStar_Tactics_Types.goal_ty =
                                    (uu___154_8572.FStar_Tactics_Types.goal_ty);
                                  FStar_Tactics_Types.opts =
                                    (uu___154_8572.FStar_Tactics_Types.opts);
                                  FStar_Tactics_Types.is_guard =
                                    (uu___154_8572.FStar_Tactics_Types.is_guard)
                                }  in
                              let g2 =
                                let uu___155_8575 = g  in
                                let uu____8576 =
                                  FStar_TypeChecker_Env.push_bv
                                    g.FStar_Tactics_Types.context v_q
                                   in
                                {
                                  FStar_Tactics_Types.context = uu____8576;
                                  FStar_Tactics_Types.witness =
                                    (uu___155_8575.FStar_Tactics_Types.witness);
                                  FStar_Tactics_Types.goal_ty =
                                    (uu___155_8575.FStar_Tactics_Types.goal_ty);
                                  FStar_Tactics_Types.opts =
                                    (uu___155_8575.FStar_Tactics_Types.opts);
                                  FStar_Tactics_Types.is_guard =
                                    (uu___155_8575.FStar_Tactics_Types.is_guard)
                                }  in
                              bind __dismiss
                                (fun uu____8583  ->
                                   let uu____8584 = add_goals [g1; g2]  in
                                   bind uu____8584
                                     (fun uu____8593  ->
                                        let uu____8594 =
                                          let uu____8599 =
                                            FStar_Syntax_Syntax.bv_to_name
                                              v_p
                                             in
                                          let uu____8600 =
                                            FStar_Syntax_Syntax.bv_to_name
                                              v_q
                                             in
                                          (uu____8599, uu____8600)  in
                                        ret uu____8594))
                          | uu____8605 ->
                              let uu____8618 =
                                tts g.FStar_Tactics_Types.context typ  in
                              fail1 "Not a disjunction: %s" uu____8618))))
       in
    FStar_All.pipe_left (wrap_err "cases") uu____8387
  
let (set_options : Prims.string -> unit tac) =
  fun s  ->
    let uu____8648 = cur_goal ()  in
    bind uu____8648
      (fun g  ->
         FStar_Options.push ();
         (let uu____8661 = FStar_Util.smap_copy g.FStar_Tactics_Types.opts
             in
          FStar_Options.set uu____8661);
         (let res = FStar_Options.set_options FStar_Options.Set s  in
          let opts' = FStar_Options.peek ()  in
          FStar_Options.pop ();
          (match res with
           | FStar_Getopt.Success  ->
               let g' =
                 let uu___156_8668 = g  in
                 {
                   FStar_Tactics_Types.context =
                     (uu___156_8668.FStar_Tactics_Types.context);
                   FStar_Tactics_Types.witness =
                     (uu___156_8668.FStar_Tactics_Types.witness);
                   FStar_Tactics_Types.goal_ty =
                     (uu___156_8668.FStar_Tactics_Types.goal_ty);
                   FStar_Tactics_Types.opts = opts';
                   FStar_Tactics_Types.is_guard =
                     (uu___156_8668.FStar_Tactics_Types.is_guard)
                 }  in
               replace_cur g'
           | FStar_Getopt.Error err ->
               fail2 "Setting options `%s` failed: %s" s err
           | FStar_Getopt.Help  ->
               fail1 "Setting options `%s` failed (got `Help`?)" s)))
  
let (top_env : unit -> env tac) =
  fun uu____8676  ->
    bind get
      (fun ps  -> FStar_All.pipe_left ret ps.FStar_Tactics_Types.main_context)
  
let (cur_env : unit -> env tac) =
  fun uu____8689  ->
    let uu____8692 = cur_goal ()  in
    bind uu____8692
      (fun g  -> FStar_All.pipe_left ret g.FStar_Tactics_Types.context)
  
let (cur_goal' : unit -> FStar_Syntax_Syntax.term tac) =
  fun uu____8705  ->
    let uu____8708 = cur_goal ()  in
    bind uu____8708
      (fun g  -> FStar_All.pipe_left ret g.FStar_Tactics_Types.goal_ty)
  
let (cur_witness : unit -> FStar_Syntax_Syntax.term tac) =
  fun uu____8721  ->
    let uu____8724 = cur_goal ()  in
    bind uu____8724
      (fun g  -> FStar_All.pipe_left ret g.FStar_Tactics_Types.witness)
  
let (unquote :
  FStar_Reflection_Data.typ ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac)
  =
  fun ty  ->
    fun tm  ->
      let uu____8745 =
        let uu____8748 = cur_goal ()  in
        bind uu____8748
          (fun goal  ->
             let env =
               FStar_TypeChecker_Env.set_expected_typ
                 goal.FStar_Tactics_Types.context ty
                in
             let uu____8756 = __tc env tm  in
             bind uu____8756
               (fun uu____8776  ->
                  match uu____8776 with
                  | (tm1,typ,guard) ->
                      let uu____8788 =
                        proc_guard "unquote" env guard
                          goal.FStar_Tactics_Types.opts
                         in
                      bind uu____8788 (fun uu____8792  -> ret tm1)))
         in
      FStar_All.pipe_left (wrap_err "unquote") uu____8745
  
let (uvar_env :
  env ->
    FStar_Reflection_Data.typ FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.term tac)
  =
  fun env  ->
    fun ty  ->
      let uu____8815 =
        match ty with
        | FStar_Pervasives_Native.Some ty1 -> ret ty1
        | FStar_Pervasives_Native.None  ->
            let uu____8821 =
              let uu____8822 = FStar_Syntax_Util.type_u ()  in
              FStar_All.pipe_left FStar_Pervasives_Native.fst uu____8822  in
            new_uvar "uvar_env.2" env uu____8821
         in
      bind uu____8815
        (fun typ  ->
           let uu____8834 = new_uvar "uvar_env" env typ  in
           bind uu____8834 (fun t  -> ret t))
  
let (unshelve : FStar_Syntax_Syntax.term -> unit tac) =
  fun t  ->
    let uu____8848 =
      bind get
        (fun ps  ->
           let env = ps.FStar_Tactics_Types.main_context  in
           let opts =
             match ps.FStar_Tactics_Types.goals with
             | g::uu____8865 -> g.FStar_Tactics_Types.opts
             | uu____8868 -> FStar_Options.peek ()  in
           let uu____8871 = FStar_Syntax_Util.head_and_args t  in
           match uu____8871 with
           | ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar ctx_uvar;
                FStar_Syntax_Syntax.pos = uu____8889;
                FStar_Syntax_Syntax.vars = uu____8890;_},uu____8891)
               ->
               let env1 =
                 let uu___157_8913 = env  in
                 {
                   FStar_TypeChecker_Env.solver =
                     (uu___157_8913.FStar_TypeChecker_Env.solver);
                   FStar_TypeChecker_Env.range =
                     (uu___157_8913.FStar_TypeChecker_Env.range);
                   FStar_TypeChecker_Env.curmodule =
                     (uu___157_8913.FStar_TypeChecker_Env.curmodule);
                   FStar_TypeChecker_Env.gamma =
                     (ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_gamma);
                   FStar_TypeChecker_Env.gamma_sig =
                     (uu___157_8913.FStar_TypeChecker_Env.gamma_sig);
                   FStar_TypeChecker_Env.gamma_cache =
                     (uu___157_8913.FStar_TypeChecker_Env.gamma_cache);
                   FStar_TypeChecker_Env.modules =
                     (uu___157_8913.FStar_TypeChecker_Env.modules);
                   FStar_TypeChecker_Env.expected_typ =
                     (uu___157_8913.FStar_TypeChecker_Env.expected_typ);
                   FStar_TypeChecker_Env.sigtab =
                     (uu___157_8913.FStar_TypeChecker_Env.sigtab);
                   FStar_TypeChecker_Env.is_pattern =
                     (uu___157_8913.FStar_TypeChecker_Env.is_pattern);
                   FStar_TypeChecker_Env.instantiate_imp =
                     (uu___157_8913.FStar_TypeChecker_Env.instantiate_imp);
                   FStar_TypeChecker_Env.effects =
                     (uu___157_8913.FStar_TypeChecker_Env.effects);
                   FStar_TypeChecker_Env.generalize =
                     (uu___157_8913.FStar_TypeChecker_Env.generalize);
                   FStar_TypeChecker_Env.letrecs =
                     (uu___157_8913.FStar_TypeChecker_Env.letrecs);
                   FStar_TypeChecker_Env.top_level =
                     (uu___157_8913.FStar_TypeChecker_Env.top_level);
                   FStar_TypeChecker_Env.check_uvars =
                     (uu___157_8913.FStar_TypeChecker_Env.check_uvars);
                   FStar_TypeChecker_Env.use_eq =
                     (uu___157_8913.FStar_TypeChecker_Env.use_eq);
                   FStar_TypeChecker_Env.is_iface =
                     (uu___157_8913.FStar_TypeChecker_Env.is_iface);
                   FStar_TypeChecker_Env.admit =
                     (uu___157_8913.FStar_TypeChecker_Env.admit);
                   FStar_TypeChecker_Env.lax =
                     (uu___157_8913.FStar_TypeChecker_Env.lax);
                   FStar_TypeChecker_Env.lax_universes =
                     (uu___157_8913.FStar_TypeChecker_Env.lax_universes);
                   FStar_TypeChecker_Env.failhard =
                     (uu___157_8913.FStar_TypeChecker_Env.failhard);
                   FStar_TypeChecker_Env.nosynth =
                     (uu___157_8913.FStar_TypeChecker_Env.nosynth);
                   FStar_TypeChecker_Env.tc_term =
                     (uu___157_8913.FStar_TypeChecker_Env.tc_term);
                   FStar_TypeChecker_Env.type_of =
                     (uu___157_8913.FStar_TypeChecker_Env.type_of);
                   FStar_TypeChecker_Env.universe_of =
                     (uu___157_8913.FStar_TypeChecker_Env.universe_of);
                   FStar_TypeChecker_Env.check_type_of =
                     (uu___157_8913.FStar_TypeChecker_Env.check_type_of);
                   FStar_TypeChecker_Env.use_bv_sorts =
                     (uu___157_8913.FStar_TypeChecker_Env.use_bv_sorts);
                   FStar_TypeChecker_Env.qtbl_name_and_index =
                     (uu___157_8913.FStar_TypeChecker_Env.qtbl_name_and_index);
                   FStar_TypeChecker_Env.normalized_eff_names =
                     (uu___157_8913.FStar_TypeChecker_Env.normalized_eff_names);
                   FStar_TypeChecker_Env.proof_ns =
                     (uu___157_8913.FStar_TypeChecker_Env.proof_ns);
                   FStar_TypeChecker_Env.synth_hook =
                     (uu___157_8913.FStar_TypeChecker_Env.synth_hook);
                   FStar_TypeChecker_Env.splice =
                     (uu___157_8913.FStar_TypeChecker_Env.splice);
                   FStar_TypeChecker_Env.is_native_tactic =
                     (uu___157_8913.FStar_TypeChecker_Env.is_native_tactic);
                   FStar_TypeChecker_Env.identifier_info =
                     (uu___157_8913.FStar_TypeChecker_Env.identifier_info);
                   FStar_TypeChecker_Env.tc_hooks =
                     (uu___157_8913.FStar_TypeChecker_Env.tc_hooks);
                   FStar_TypeChecker_Env.dsenv =
                     (uu___157_8913.FStar_TypeChecker_Env.dsenv);
                   FStar_TypeChecker_Env.dep_graph =
                     (uu___157_8913.FStar_TypeChecker_Env.dep_graph)
                 }  in
               let uu____8914 =
                 let uu____8917 =
                   let uu____8918 = bnorm env1 t  in
                   let uu____8919 =
                     bnorm env1 ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_typ  in
                   {
                     FStar_Tactics_Types.context = env1;
                     FStar_Tactics_Types.witness = uu____8918;
                     FStar_Tactics_Types.goal_ty = uu____8919;
                     FStar_Tactics_Types.opts = opts;
                     FStar_Tactics_Types.is_guard = false
                   }  in
                 [uu____8917]  in
               add_goals uu____8914
           | uu____8920 -> fail "not a uvar")
       in
    FStar_All.pipe_left (wrap_err "unshelve") uu____8848
  
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
          (fun uu____8981  ->
             let uu____8982 = FStar_Options.unsafe_tactic_exec ()  in
             if uu____8982
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
        (fun uu____9003  ->
           let uu____9004 =
             FStar_Syntax_Syntax.gen_bv nm FStar_Pervasives_Native.None t  in
           ret uu____9004)
  
let (change : FStar_Reflection_Data.typ -> unit tac) =
  fun ty  ->
    let uu____9014 =
      mlog
        (fun uu____9019  ->
           let uu____9020 = FStar_Syntax_Print.term_to_string ty  in
           FStar_Util.print1 "change: ty = %s\n" uu____9020)
        (fun uu____9023  ->
           let uu____9024 = cur_goal ()  in
           bind uu____9024
             (fun g  ->
                let uu____9030 = __tc g.FStar_Tactics_Types.context ty  in
                bind uu____9030
                  (fun uu____9050  ->
                     match uu____9050 with
                     | (ty1,uu____9060,guard) ->
                         let uu____9062 =
                           proc_guard "change" g.FStar_Tactics_Types.context
                             guard g.FStar_Tactics_Types.opts
                            in
                         bind uu____9062
                           (fun uu____9067  ->
                              let uu____9068 =
                                do_unify g.FStar_Tactics_Types.context
                                  g.FStar_Tactics_Types.goal_ty ty1
                                 in
                              bind uu____9068
                                (fun bb  ->
                                   if bb
                                   then
                                     replace_cur
                                       (let uu___158_9077 = g  in
                                        {
                                          FStar_Tactics_Types.context =
                                            (uu___158_9077.FStar_Tactics_Types.context);
                                          FStar_Tactics_Types.witness =
                                            (uu___158_9077.FStar_Tactics_Types.witness);
                                          FStar_Tactics_Types.goal_ty = ty1;
                                          FStar_Tactics_Types.opts =
                                            (uu___158_9077.FStar_Tactics_Types.opts);
                                          FStar_Tactics_Types.is_guard =
                                            (uu___158_9077.FStar_Tactics_Types.is_guard)
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
                                      let uu____9084 =
                                        do_unify
                                          g.FStar_Tactics_Types.context ng
                                          nty
                                         in
                                      bind uu____9084
                                        (fun b  ->
                                           if b
                                           then
                                             replace_cur
                                               (let uu___159_9093 = g  in
                                                {
                                                  FStar_Tactics_Types.context
                                                    =
                                                    (uu___159_9093.FStar_Tactics_Types.context);
                                                  FStar_Tactics_Types.witness
                                                    =
                                                    (uu___159_9093.FStar_Tactics_Types.witness);
                                                  FStar_Tactics_Types.goal_ty
                                                    = ty1;
                                                  FStar_Tactics_Types.opts =
                                                    (uu___159_9093.FStar_Tactics_Types.opts);
                                                  FStar_Tactics_Types.is_guard
                                                    =
                                                    (uu___159_9093.FStar_Tactics_Types.is_guard)
                                                })
                                           else fail "not convertible")))))))
       in
    FStar_All.pipe_left (wrap_err "change") uu____9014
  
let rec last : 'a . 'a Prims.list -> 'a =
  fun l  ->
    match l with
    | [] -> failwith "last: empty list"
    | x::[] -> x
    | uu____9115::xs -> last xs
  
let rec init : 'a . 'a Prims.list -> 'a Prims.list =
  fun l  ->
    match l with
    | [] -> failwith "init: empty list"
    | x::[] -> []
    | x::xs -> let uu____9143 = init xs  in x :: uu____9143
  
let rec (inspect :
  FStar_Syntax_Syntax.term -> FStar_Reflection_Data.term_view tac) =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t  in
    let t2 = FStar_Syntax_Util.un_uinst t1  in
    match t2.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_meta (t3,uu____9160) -> inspect t3
    | FStar_Syntax_Syntax.Tm_name bv ->
        FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_Var bv)
    | FStar_Syntax_Syntax.Tm_bvar bv ->
        FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_BVar bv)
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_FVar fv)
    | FStar_Syntax_Syntax.Tm_app (hd1,[]) ->
        failwith "inspect: empty arguments on Tm_app"
    | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
        let uu____9217 = last args  in
        (match uu____9217 with
         | (a,q) ->
             let q' = FStar_Reflection_Basic.inspect_aqual q  in
             let uu____9239 =
               let uu____9240 =
                 let uu____9245 =
                   let uu____9246 =
                     let uu____9251 = init args  in
                     FStar_Syntax_Syntax.mk_Tm_app hd1 uu____9251  in
                   uu____9246 FStar_Pervasives_Native.None
                     t2.FStar_Syntax_Syntax.pos
                    in
                 (uu____9245, (a, q'))  in
               FStar_Reflection_Data.Tv_App uu____9240  in
             FStar_All.pipe_left ret uu____9239)
    | FStar_Syntax_Syntax.Tm_abs ([],uu____9262,uu____9263) ->
        failwith "inspect: empty arguments on Tm_abs"
    | FStar_Syntax_Syntax.Tm_abs (bs,t3,k) ->
        let uu____9307 = FStar_Syntax_Subst.open_term bs t3  in
        (match uu____9307 with
         | (bs1,t4) ->
             (match bs1 with
              | [] -> failwith "impossible"
              | b::bs2 ->
                  let uu____9340 =
                    let uu____9341 =
                      let uu____9346 = FStar_Syntax_Util.abs bs2 t4 k  in
                      (b, uu____9346)  in
                    FStar_Reflection_Data.Tv_Abs uu____9341  in
                  FStar_All.pipe_left ret uu____9340))
    | FStar_Syntax_Syntax.Tm_type uu____9349 ->
        FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_Type ())
    | FStar_Syntax_Syntax.Tm_arrow ([],k) ->
        failwith "inspect: empty binders on arrow"
    | FStar_Syntax_Syntax.Tm_arrow uu____9369 ->
        let uu____9382 = FStar_Syntax_Util.arrow_one t2  in
        (match uu____9382 with
         | FStar_Pervasives_Native.Some (b,c) ->
             FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_Arrow (b, c))
         | FStar_Pervasives_Native.None  -> failwith "impossible")
    | FStar_Syntax_Syntax.Tm_refine (bv,t3) ->
        let b = FStar_Syntax_Syntax.mk_binder bv  in
        let uu____9412 = FStar_Syntax_Subst.open_term [b] t3  in
        (match uu____9412 with
         | (b',t4) ->
             let b1 =
               match b' with
               | b'1::[] -> b'1
               | uu____9451 -> failwith "impossible"  in
             FStar_All.pipe_left ret
               (FStar_Reflection_Data.Tv_Refine
                  ((FStar_Pervasives_Native.fst b1), t4)))
    | FStar_Syntax_Syntax.Tm_constant c ->
        let uu____9459 =
          let uu____9460 = FStar_Reflection_Basic.inspect_const c  in
          FStar_Reflection_Data.Tv_Const uu____9460  in
        FStar_All.pipe_left ret uu____9459
    | FStar_Syntax_Syntax.Tm_uvar ctx_u ->
        let uu____9464 =
          let uu____9465 =
            let uu____9474 =
              let uu____9475 =
                FStar_Syntax_Unionfind.uvar_id
                  ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
                 in
              FStar_BigInt.of_int_fs uu____9475  in
            (uu____9474, (ctx_u.FStar_Syntax_Syntax.ctx_uvar_gamma),
              (ctx_u.FStar_Syntax_Syntax.ctx_uvar_binders),
              (ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ))
             in
          FStar_Reflection_Data.Tv_Uvar uu____9465  in
        FStar_All.pipe_left ret uu____9464
    | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),t21) ->
        if lb.FStar_Syntax_Syntax.lbunivs <> []
        then FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
        else
          (match lb.FStar_Syntax_Syntax.lbname with
           | FStar_Util.Inr uu____9501 ->
               FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
           | FStar_Util.Inl bv ->
               let b = FStar_Syntax_Syntax.mk_binder bv  in
               let uu____9506 = FStar_Syntax_Subst.open_term [b] t21  in
               (match uu____9506 with
                | (bs,t22) ->
                    let b1 =
                      match bs with
                      | b1::[] -> b1
                      | uu____9545 ->
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
           | FStar_Util.Inr uu____9575 ->
               FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
           | FStar_Util.Inl bv ->
               let uu____9579 = FStar_Syntax_Subst.open_let_rec [lb] t21  in
               (match uu____9579 with
                | (lbs,t22) ->
                    (match lbs with
                     | lb1::[] ->
                         (match lb1.FStar_Syntax_Syntax.lbname with
                          | FStar_Util.Inr uu____9599 ->
                              ret FStar_Reflection_Data.Tv_Unknown
                          | FStar_Util.Inl bv1 ->
                              FStar_All.pipe_left ret
                                (FStar_Reflection_Data.Tv_Let
                                   (true, bv1,
                                     (lb1.FStar_Syntax_Syntax.lbdef), t22)))
                     | uu____9603 ->
                         failwith
                           "impossible: open_term returned different amount of binders")))
    | FStar_Syntax_Syntax.Tm_match (t3,brs) ->
        let rec inspect_pat p =
          match p.FStar_Syntax_Syntax.v with
          | FStar_Syntax_Syntax.Pat_constant c ->
              let uu____9657 = FStar_Reflection_Basic.inspect_const c  in
              FStar_Reflection_Data.Pat_Constant uu____9657
          | FStar_Syntax_Syntax.Pat_cons (fv,ps) ->
              let uu____9676 =
                let uu____9683 =
                  FStar_List.map
                    (fun uu____9695  ->
                       match uu____9695 with
                       | (p1,uu____9703) -> inspect_pat p1) ps
                   in
                (fv, uu____9683)  in
              FStar_Reflection_Data.Pat_Cons uu____9676
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
            (fun uu___91_9787  ->
               match uu___91_9787 with
               | (pat,uu____9805,t4) ->
                   let uu____9819 = inspect_pat pat  in (uu____9819, t4))
            brs1
           in
        FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_Match (t3, brs2))
    | FStar_Syntax_Syntax.Tm_unknown  ->
        FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
    | uu____9826 ->
        ((let uu____9828 =
            let uu____9833 =
              let uu____9834 = FStar_Syntax_Print.tag_of_term t2  in
              let uu____9835 = FStar_Syntax_Print.term_to_string t2  in
              FStar_Util.format2
                "inspect: outside of expected syntax (%s, %s)\n" uu____9834
                uu____9835
               in
            (FStar_Errors.Warning_CantInspect, uu____9833)  in
          FStar_Errors.log_issue t2.FStar_Syntax_Syntax.pos uu____9828);
         FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown)
  
let (pack : FStar_Reflection_Data.term_view -> FStar_Syntax_Syntax.term tac)
  =
  fun tv  ->
    match tv with
    | FStar_Reflection_Data.Tv_Var bv ->
        let uu____9848 = FStar_Syntax_Syntax.bv_to_name bv  in
        FStar_All.pipe_left ret uu____9848
    | FStar_Reflection_Data.Tv_BVar bv ->
        let uu____9852 = FStar_Syntax_Syntax.bv_to_tm bv  in
        FStar_All.pipe_left ret uu____9852
    | FStar_Reflection_Data.Tv_FVar fv ->
        let uu____9856 = FStar_Syntax_Syntax.fv_to_tm fv  in
        FStar_All.pipe_left ret uu____9856
    | FStar_Reflection_Data.Tv_App (l,(r,q)) ->
        let q' = FStar_Reflection_Basic.pack_aqual q  in
        let uu____9863 = FStar_Syntax_Util.mk_app l [(r, q')]  in
        FStar_All.pipe_left ret uu____9863
    | FStar_Reflection_Data.Tv_Abs (b,t) ->
        let uu____9886 =
          FStar_Syntax_Util.abs [b] t FStar_Pervasives_Native.None  in
        FStar_All.pipe_left ret uu____9886
    | FStar_Reflection_Data.Tv_Arrow (b,c) ->
        let uu____9903 = FStar_Syntax_Util.arrow [b] c  in
        FStar_All.pipe_left ret uu____9903
    | FStar_Reflection_Data.Tv_Type () ->
        FStar_All.pipe_left ret FStar_Syntax_Util.ktype
    | FStar_Reflection_Data.Tv_Refine (bv,t) ->
        let uu____9922 = FStar_Syntax_Util.refine bv t  in
        FStar_All.pipe_left ret uu____9922
    | FStar_Reflection_Data.Tv_Const c ->
        let uu____9930 =
          let uu____9933 =
            let uu____9940 =
              let uu____9941 = FStar_Reflection_Basic.pack_const c  in
              FStar_Syntax_Syntax.Tm_constant uu____9941  in
            FStar_Syntax_Syntax.mk uu____9940  in
          uu____9933 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
        FStar_All.pipe_left ret uu____9930
    | FStar_Reflection_Data.Tv_Uvar (u,g,bs,t) ->
        let uu____9953 =
          let uu____9956 = FStar_BigInt.to_int_fs u  in
          FStar_Syntax_Util.uvar_from_id uu____9956 (g, bs, t)  in
        FStar_All.pipe_left ret uu____9953
    | FStar_Reflection_Data.Tv_Let (false ,bv,t1,t2) ->
        let lb =
          FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl bv) []
            bv.FStar_Syntax_Syntax.sort FStar_Parser_Const.effect_Tot_lid t1
            [] FStar_Range.dummyRange
           in
        let uu____9977 =
          let uu____9980 =
            let uu____9987 =
              let uu____9988 =
                let uu____10001 =
                  let uu____10004 =
                    let uu____10005 = FStar_Syntax_Syntax.mk_binder bv  in
                    [uu____10005]  in
                  FStar_Syntax_Subst.close uu____10004 t2  in
                ((false, [lb]), uu____10001)  in
              FStar_Syntax_Syntax.Tm_let uu____9988  in
            FStar_Syntax_Syntax.mk uu____9987  in
          uu____9980 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
        FStar_All.pipe_left ret uu____9977
    | FStar_Reflection_Data.Tv_Let (true ,bv,t1,t2) ->
        let lb =
          FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl bv) []
            bv.FStar_Syntax_Syntax.sort FStar_Parser_Const.effect_Tot_lid t1
            [] FStar_Range.dummyRange
           in
        let uu____10041 = FStar_Syntax_Subst.close_let_rec [lb] t2  in
        (match uu____10041 with
         | (lbs,body) ->
             let uu____10056 =
               FStar_Syntax_Syntax.mk
                 (FStar_Syntax_Syntax.Tm_let ((true, lbs), body))
                 FStar_Pervasives_Native.None FStar_Range.dummyRange
                in
             FStar_All.pipe_left ret uu____10056)
    | FStar_Reflection_Data.Tv_Match (t,brs) ->
        let wrap v1 =
          {
            FStar_Syntax_Syntax.v = v1;
            FStar_Syntax_Syntax.p = FStar_Range.dummyRange
          }  in
        let rec pack_pat p =
          match p with
          | FStar_Reflection_Data.Pat_Constant c ->
              let uu____10094 =
                let uu____10095 = FStar_Reflection_Basic.pack_const c  in
                FStar_Syntax_Syntax.Pat_constant uu____10095  in
              FStar_All.pipe_left wrap uu____10094
          | FStar_Reflection_Data.Pat_Cons (fv,ps) ->
              let uu____10102 =
                let uu____10103 =
                  let uu____10116 =
                    FStar_List.map
                      (fun p1  ->
                         let uu____10132 = pack_pat p1  in
                         (uu____10132, false)) ps
                     in
                  (fv, uu____10116)  in
                FStar_Syntax_Syntax.Pat_cons uu____10103  in
              FStar_All.pipe_left wrap uu____10102
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
            (fun uu___92_10178  ->
               match uu___92_10178 with
               | (pat,t1) ->
                   let uu____10195 = pack_pat pat  in
                   (uu____10195, FStar_Pervasives_Native.None, t1)) brs
           in
        let brs2 = FStar_List.map FStar_Syntax_Subst.close_branch brs1  in
        let uu____10243 =
          FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_match (t, brs2))
            FStar_Pervasives_Native.None FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____10243
    | FStar_Reflection_Data.Tv_AscribedT (e,t,tacopt) ->
        let uu____10275 =
          FStar_Syntax_Syntax.mk
            (FStar_Syntax_Syntax.Tm_ascribed
               (e, ((FStar_Util.Inl t), tacopt),
                 FStar_Pervasives_Native.None)) FStar_Pervasives_Native.None
            FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____10275
    | FStar_Reflection_Data.Tv_AscribedC (e,c,tacopt) ->
        let uu____10325 =
          FStar_Syntax_Syntax.mk
            (FStar_Syntax_Syntax.Tm_ascribed
               (e, ((FStar_Util.Inr c), tacopt),
                 FStar_Pervasives_Native.None)) FStar_Pervasives_Native.None
            FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____10325
    | FStar_Reflection_Data.Tv_Unknown  ->
        let uu____10368 =
          FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
            FStar_Pervasives_Native.None FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____10368
  
let (goal_of_goal_ty :
  env ->
    FStar_Reflection_Data.typ ->
      (FStar_Tactics_Types.goal,FStar_TypeChecker_Env.guard_t)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun typ  ->
      let uu____10389 =
        FStar_TypeChecker_Util.new_implicit_var "proofstate_of_goal_ty"
          typ.FStar_Syntax_Syntax.pos env typ
         in
      match uu____10389 with
      | (u,uu____10407,g_u) ->
          let g =
            let uu____10422 = FStar_Options.peek ()  in
            {
              FStar_Tactics_Types.context = env;
              FStar_Tactics_Types.witness = u;
              FStar_Tactics_Types.goal_ty = typ;
              FStar_Tactics_Types.opts = uu____10422;
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
      let uu____10437 = goal_of_goal_ty env typ  in
      match uu____10437 with
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
  