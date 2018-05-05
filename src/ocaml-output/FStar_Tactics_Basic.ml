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
                  let uu____2782 =
                    let uu____2785 =
                      let uu____2786 = FStar_Syntax_Syntax.mk_Total typ'  in
                      FStar_Syntax_Util.arrow [b] uu____2786  in
                    new_uvar "intro" goal.FStar_Tactics_Types.context
                      uu____2785
                     in
                  bind uu____2782
                    (fun u  ->
                       let body =
                         let uu____2804 =
                           let uu____2809 =
                             let uu____2810 =
                               let uu____2817 =
                                 FStar_Syntax_Syntax.bv_to_name
                                   (FStar_Pervasives_Native.fst b)
                                  in
                               (uu____2817, (FStar_Pervasives_Native.snd b))
                                in
                             [uu____2810]  in
                           FStar_Syntax_Syntax.mk_Tm_app u uu____2809  in
                         uu____2804 FStar_Pervasives_Native.None
                           u.FStar_Syntax_Syntax.pos
                          in
                       let uu____2836 =
                         let uu____2839 =
                           FStar_Syntax_Util.abs [b] body
                             FStar_Pervasives_Native.None
                            in
                         trysolve goal uu____2839  in
                       bind uu____2836
                         (fun bb  ->
                            if bb
                            then
                              let uu____2853 =
                                let uu____2856 =
                                  let uu___119_2857 = goal  in
                                  let uu____2858 = bnorm env' body  in
                                  let uu____2859 = bnorm env' typ'  in
                                  {
                                    FStar_Tactics_Types.context = env';
                                    FStar_Tactics_Types.witness = uu____2858;
                                    FStar_Tactics_Types.goal_ty = uu____2859;
                                    FStar_Tactics_Types.opts =
                                      (uu___119_2857.FStar_Tactics_Types.opts);
                                    FStar_Tactics_Types.is_guard =
                                      (uu___119_2857.FStar_Tactics_Types.is_guard)
                                  }  in
                                replace_cur uu____2856  in
                              bind uu____2853 (fun uu____2861  -> ret b)
                            else fail "unification failed")))
           | FStar_Pervasives_Native.None  ->
               let uu____2867 =
                 tts goal.FStar_Tactics_Types.context
                   goal.FStar_Tactics_Types.goal_ty
                  in
               fail1 "goal is not an arrow (%s)" uu____2867)
       in
    FStar_All.pipe_left (wrap_err "intro") uu____2740
  
let (intro_rec :
  unit ->
    (FStar_Syntax_Syntax.binder,FStar_Syntax_Syntax.binder)
      FStar_Pervasives_Native.tuple2 tac)
  =
  fun uu____2882  ->
    let uu____2889 = cur_goal ()  in
    bind uu____2889
      (fun goal  ->
         FStar_Util.print_string
           "WARNING (intro_rec): calling this is known to cause normalizer loops\n";
         FStar_Util.print_string
           "WARNING (intro_rec): proceed at your own risk...\n";
         (let uu____2906 =
            FStar_Syntax_Util.arrow_one goal.FStar_Tactics_Types.goal_ty  in
          match uu____2906 with
          | FStar_Pervasives_Native.Some (b,c) ->
              let uu____2925 =
                let uu____2926 = FStar_Syntax_Util.is_total_comp c  in
                Prims.op_Negation uu____2926  in
              if uu____2925
              then fail "Codomain is effectful"
              else
                (let bv =
                   FStar_Syntax_Syntax.gen_bv "__recf"
                     FStar_Pervasives_Native.None
                     goal.FStar_Tactics_Types.goal_ty
                    in
                 let bs =
                   let uu____2946 = FStar_Syntax_Syntax.mk_binder bv  in
                   [uu____2946; b]  in
                 let env' =
                   FStar_TypeChecker_Env.push_binders
                     goal.FStar_Tactics_Types.context bs
                    in
                 let uu____2964 =
                   let uu____2967 = comp_to_typ c  in
                   new_uvar "intro_rec" env' uu____2967  in
                 bind uu____2964
                   (fun u  ->
                      let lb =
                        let uu____2982 =
                          FStar_Syntax_Util.abs [b] u
                            FStar_Pervasives_Native.None
                           in
                        FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl bv)
                          [] goal.FStar_Tactics_Types.goal_ty
                          FStar_Parser_Const.effect_Tot_lid uu____2982 []
                          FStar_Range.dummyRange
                         in
                      let body = FStar_Syntax_Syntax.bv_to_name bv  in
                      let uu____2996 =
                        FStar_Syntax_Subst.close_let_rec [lb] body  in
                      match uu____2996 with
                      | (lbs,body1) ->
                          let tm =
                            FStar_Syntax_Syntax.mk
                              (FStar_Syntax_Syntax.Tm_let
                                 ((true, lbs), body1))
                              FStar_Pervasives_Native.None
                              (goal.FStar_Tactics_Types.witness).FStar_Syntax_Syntax.pos
                             in
                          let uu____3028 = trysolve goal tm  in
                          bind uu____3028
                            (fun bb  ->
                               if bb
                               then
                                 let uu____3044 =
                                   let uu____3047 =
                                     let uu___120_3048 = goal  in
                                     let uu____3049 = bnorm env' u  in
                                     let uu____3050 =
                                       let uu____3051 = comp_to_typ c  in
                                       bnorm env' uu____3051  in
                                     {
                                       FStar_Tactics_Types.context = env';
                                       FStar_Tactics_Types.witness =
                                         uu____3049;
                                       FStar_Tactics_Types.goal_ty =
                                         uu____3050;
                                       FStar_Tactics_Types.opts =
                                         (uu___120_3048.FStar_Tactics_Types.opts);
                                       FStar_Tactics_Types.is_guard =
                                         (uu___120_3048.FStar_Tactics_Types.is_guard)
                                     }  in
                                   replace_cur uu____3047  in
                                 bind uu____3044
                                   (fun uu____3058  ->
                                      let uu____3059 =
                                        let uu____3064 =
                                          FStar_Syntax_Syntax.mk_binder bv
                                           in
                                        (uu____3064, b)  in
                                      ret uu____3059)
                               else fail "intro_rec: unification failed")))
          | FStar_Pervasives_Native.None  ->
              let uu____3078 =
                tts goal.FStar_Tactics_Types.context
                  goal.FStar_Tactics_Types.goal_ty
                 in
              fail1 "intro_rec: goal is not an arrow (%s)" uu____3078))
  
let (norm : FStar_Syntax_Embeddings.norm_step Prims.list -> unit tac) =
  fun s  ->
    let uu____3096 = cur_goal ()  in
    bind uu____3096
      (fun goal  ->
         mlog
           (fun uu____3103  ->
              let uu____3104 =
                FStar_Syntax_Print.term_to_string
                  goal.FStar_Tactics_Types.witness
                 in
              FStar_Util.print1 "norm: witness = %s\n" uu____3104)
           (fun uu____3109  ->
              let steps =
                let uu____3113 = FStar_TypeChecker_Normalize.tr_norm_steps s
                   in
                FStar_List.append
                  [FStar_TypeChecker_Normalize.Reify;
                  FStar_TypeChecker_Normalize.UnfoldTac] uu____3113
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
                (let uu___121_3120 = goal  in
                 {
                   FStar_Tactics_Types.context =
                     (uu___121_3120.FStar_Tactics_Types.context);
                   FStar_Tactics_Types.witness = w;
                   FStar_Tactics_Types.goal_ty = t;
                   FStar_Tactics_Types.opts =
                     (uu___121_3120.FStar_Tactics_Types.opts);
                   FStar_Tactics_Types.is_guard =
                     (uu___121_3120.FStar_Tactics_Types.is_guard)
                 })))
  
let (norm_term_env :
  env ->
    FStar_Syntax_Embeddings.norm_step Prims.list ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac)
  =
  fun e  ->
    fun s  ->
      fun t  ->
        let uu____3144 =
          mlog
            (fun uu____3149  ->
               let uu____3150 = FStar_Syntax_Print.term_to_string t  in
               FStar_Util.print1 "norm_term: tm = %s\n" uu____3150)
            (fun uu____3152  ->
               bind get
                 (fun ps  ->
                    let opts =
                      match ps.FStar_Tactics_Types.goals with
                      | g::uu____3158 -> g.FStar_Tactics_Types.opts
                      | uu____3161 -> FStar_Options.peek ()  in
                    mlog
                      (fun uu____3166  ->
                         let uu____3167 =
                           tts ps.FStar_Tactics_Types.main_context t  in
                         FStar_Util.print1 "norm_term_env: t = %s\n"
                           uu____3167)
                      (fun uu____3170  ->
                         let uu____3171 = __tc e t  in
                         bind uu____3171
                           (fun uu____3192  ->
                              match uu____3192 with
                              | (t1,uu____3202,uu____3203) ->
                                  let steps =
                                    let uu____3207 =
                                      FStar_TypeChecker_Normalize.tr_norm_steps
                                        s
                                       in
                                    FStar_List.append
                                      [FStar_TypeChecker_Normalize.Reify;
                                      FStar_TypeChecker_Normalize.UnfoldTac]
                                      uu____3207
                                     in
                                  let t2 =
                                    normalize steps
                                      ps.FStar_Tactics_Types.main_context t1
                                     in
                                  ret t2))))
           in
        FStar_All.pipe_left (wrap_err "norm_term") uu____3144
  
let (refine_intro : unit -> unit tac) =
  fun uu____3221  ->
    let uu____3224 =
      let uu____3227 = cur_goal ()  in
      bind uu____3227
        (fun g  ->
           let uu____3234 =
             FStar_TypeChecker_Rel.base_and_refinement
               g.FStar_Tactics_Types.context g.FStar_Tactics_Types.goal_ty
              in
           match uu____3234 with
           | (uu____3247,FStar_Pervasives_Native.None ) ->
               fail "not a refinement"
           | (t,FStar_Pervasives_Native.Some (bv,phi)) ->
               let g1 =
                 let uu___122_3272 = g  in
                 {
                   FStar_Tactics_Types.context =
                     (uu___122_3272.FStar_Tactics_Types.context);
                   FStar_Tactics_Types.witness =
                     (uu___122_3272.FStar_Tactics_Types.witness);
                   FStar_Tactics_Types.goal_ty = t;
                   FStar_Tactics_Types.opts =
                     (uu___122_3272.FStar_Tactics_Types.opts);
                   FStar_Tactics_Types.is_guard =
                     (uu___122_3272.FStar_Tactics_Types.is_guard)
                 }  in
               let uu____3273 =
                 let uu____3278 =
                   let uu____3283 =
                     let uu____3284 = FStar_Syntax_Syntax.mk_binder bv  in
                     [uu____3284]  in
                   FStar_Syntax_Subst.open_term uu____3283 phi  in
                 match uu____3278 with
                 | (bvs,phi1) ->
                     let uu____3303 =
                       let uu____3304 = FStar_List.hd bvs  in
                       FStar_Pervasives_Native.fst uu____3304  in
                     (uu____3303, phi1)
                  in
               (match uu____3273 with
                | (bv1,phi1) ->
                    let uu____3317 =
                      let uu____3320 =
                        FStar_Syntax_Subst.subst
                          [FStar_Syntax_Syntax.NT
                             (bv1, (g.FStar_Tactics_Types.witness))] phi1
                         in
                      mk_irrelevant_goal "refine_intro refinement"
                        g.FStar_Tactics_Types.context uu____3320
                        g.FStar_Tactics_Types.opts
                       in
                    bind uu____3317
                      (fun g2  ->
                         bind __dismiss
                           (fun uu____3326  -> add_goals [g1; g2]))))
       in
    FStar_All.pipe_left (wrap_err "refine_intro") uu____3224
  
let (__exact_now : Prims.bool -> FStar_Syntax_Syntax.term -> unit tac) =
  fun set_expected_typ1  ->
    fun t  ->
      let uu____3345 = cur_goal ()  in
      bind uu____3345
        (fun goal  ->
           let env =
             if set_expected_typ1
             then
               FStar_TypeChecker_Env.set_expected_typ
                 goal.FStar_Tactics_Types.context
                 goal.FStar_Tactics_Types.goal_ty
             else goal.FStar_Tactics_Types.context  in
           let uu____3354 = __tc env t  in
           bind uu____3354
             (fun uu____3373  ->
                match uu____3373 with
                | (t1,typ,guard) ->
                    mlog
                      (fun uu____3388  ->
                         let uu____3389 =
                           tts goal.FStar_Tactics_Types.context typ  in
                         let uu____3390 =
                           FStar_TypeChecker_Rel.guard_to_string
                             goal.FStar_Tactics_Types.context guard
                            in
                         FStar_Util.print2
                           "__exact_now: got type %s\n__exact_now and guard %s\n"
                           uu____3389 uu____3390)
                      (fun uu____3393  ->
                         let uu____3394 =
                           proc_guard "__exact typing"
                             goal.FStar_Tactics_Types.context guard
                             goal.FStar_Tactics_Types.opts
                            in
                         bind uu____3394
                           (fun uu____3398  ->
                              mlog
                                (fun uu____3402  ->
                                   let uu____3403 =
                                     tts goal.FStar_Tactics_Types.context typ
                                      in
                                   let uu____3404 =
                                     tts goal.FStar_Tactics_Types.context
                                       goal.FStar_Tactics_Types.goal_ty
                                      in
                                   FStar_Util.print2
                                     "__exact_now: unifying %s and %s\n"
                                     uu____3403 uu____3404)
                                (fun uu____3407  ->
                                   let uu____3408 =
                                     do_unify
                                       goal.FStar_Tactics_Types.context typ
                                       goal.FStar_Tactics_Types.goal_ty
                                      in
                                   bind uu____3408
                                     (fun b  ->
                                        if b
                                        then solve goal t1
                                        else
                                          (let uu____3416 =
                                             tts
                                               goal.FStar_Tactics_Types.context
                                               t1
                                              in
                                           let uu____3417 =
                                             tts
                                               goal.FStar_Tactics_Types.context
                                               typ
                                              in
                                           let uu____3418 =
                                             tts
                                               goal.FStar_Tactics_Types.context
                                               goal.FStar_Tactics_Types.goal_ty
                                              in
                                           let uu____3419 =
                                             tts
                                               goal.FStar_Tactics_Types.context
                                               goal.FStar_Tactics_Types.witness
                                              in
                                           fail4
                                             "%s : %s does not exactly solve the goal %s (witness = %s)"
                                             uu____3416 uu____3417 uu____3418
                                             uu____3419)))))))
  
let (t_exact : Prims.bool -> FStar_Syntax_Syntax.term -> unit tac) =
  fun set_expected_typ1  ->
    fun tm  ->
      let uu____3434 =
        mlog
          (fun uu____3439  ->
             let uu____3440 = FStar_Syntax_Print.term_to_string tm  in
             FStar_Util.print1 "t_exact: tm = %s\n" uu____3440)
          (fun uu____3443  ->
             let uu____3444 =
               let uu____3451 = __exact_now set_expected_typ1 tm  in
               trytac' uu____3451  in
             bind uu____3444
               (fun uu___88_3460  ->
                  match uu___88_3460 with
                  | FStar_Util.Inr r -> ret ()
                  | FStar_Util.Inl e ->
                      let uu____3469 =
                        let uu____3476 =
                          let uu____3479 =
                            norm [FStar_Syntax_Embeddings.Delta]  in
                          bind uu____3479
                            (fun uu____3484  ->
                               let uu____3485 = refine_intro ()  in
                               bind uu____3485
                                 (fun uu____3489  ->
                                    __exact_now set_expected_typ1 tm))
                           in
                        trytac' uu____3476  in
                      bind uu____3469
                        (fun uu___87_3496  ->
                           match uu___87_3496 with
                           | FStar_Util.Inr r -> ret ()
                           | FStar_Util.Inl uu____3504 -> fail e)))
         in
      FStar_All.pipe_left (wrap_err "exact") uu____3434
  
let (uvar_free_in_goal :
  FStar_Syntax_Syntax.uvar -> FStar_Tactics_Types.goal -> Prims.bool) =
  fun u  ->
    fun g  ->
      if g.FStar_Tactics_Types.is_guard
      then false
      else
        (let free_uvars =
           let uu____3533 =
             let uu____3536 =
               FStar_Syntax_Free.uvars g.FStar_Tactics_Types.goal_ty  in
             FStar_Util.set_elements uu____3536  in
           FStar_List.map (fun u1  -> u1.FStar_Syntax_Syntax.ctx_uvar_head)
             uu____3533
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
          let uu____3616 = f x  in
          bind uu____3616
            (fun y  ->
               let uu____3624 = mapM f xs  in
               bind uu____3624 (fun ys  -> ret (y :: ys)))
  
exception NoUnif 
let (uu___is_NoUnif : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with | NoUnif  -> true | uu____3644 -> false
  
let rec (__apply :
  Prims.bool ->
    FStar_Syntax_Syntax.term -> FStar_Reflection_Data.typ -> unit tac)
  =
  fun uopt  ->
    fun tm  ->
      fun typ  ->
        let uu____3664 = cur_goal ()  in
        bind uu____3664
          (fun goal  ->
             mlog
               (fun uu____3671  ->
                  let uu____3672 = FStar_Syntax_Print.term_to_string tm  in
                  FStar_Util.print1 ">>> Calling __exact(%s)\n" uu____3672)
               (fun uu____3675  ->
                  let uu____3676 =
                    let uu____3681 =
                      let uu____3684 = t_exact false tm  in
                      with_policy FStar_Tactics_Types.Force uu____3684  in
                    trytac_exn uu____3681  in
                  bind uu____3676
                    (fun uu___89_3691  ->
                       match uu___89_3691 with
                       | FStar_Pervasives_Native.Some r -> ret ()
                       | FStar_Pervasives_Native.None  ->
                           mlog
                             (fun uu____3699  ->
                                let uu____3700 =
                                  FStar_Syntax_Print.term_to_string typ  in
                                FStar_Util.print1 ">>> typ = %s\n" uu____3700)
                             (fun uu____3703  ->
                                let uu____3704 =
                                  FStar_Syntax_Util.arrow_one typ  in
                                match uu____3704 with
                                | FStar_Pervasives_Native.None  ->
                                    FStar_Exn.raise NoUnif
                                | FStar_Pervasives_Native.Some ((bv,aq),c) ->
                                    mlog
                                      (fun uu____3728  ->
                                         let uu____3729 =
                                           FStar_Syntax_Print.binder_to_string
                                             (bv, aq)
                                            in
                                         FStar_Util.print1
                                           "__apply: pushing binder %s\n"
                                           uu____3729)
                                      (fun uu____3732  ->
                                         let uu____3733 =
                                           let uu____3734 =
                                             FStar_Syntax_Util.is_total_comp
                                               c
                                              in
                                           Prims.op_Negation uu____3734  in
                                         if uu____3733
                                         then
                                           fail "apply: not total codomain"
                                         else
                                           (let uu____3738 =
                                              new_uvar "apply"
                                                goal.FStar_Tactics_Types.context
                                                bv.FStar_Syntax_Syntax.sort
                                               in
                                            bind uu____3738
                                              (fun u  ->
                                                 let tm' =
                                                   FStar_Syntax_Syntax.mk_Tm_app
                                                     tm [(u, aq)]
                                                     FStar_Pervasives_Native.None
                                                     tm.FStar_Syntax_Syntax.pos
                                                    in
                                                 let typ' =
                                                   let uu____3764 =
                                                     comp_to_typ c  in
                                                   FStar_All.pipe_left
                                                     (FStar_Syntax_Subst.subst
                                                        [FStar_Syntax_Syntax.NT
                                                           (bv, u)])
                                                     uu____3764
                                                    in
                                                 let uu____3767 =
                                                   __apply uopt tm' typ'  in
                                                 bind uu____3767
                                                   (fun uu____3781  ->
                                                      let u1 =
                                                        bnorm
                                                          goal.FStar_Tactics_Types.context
                                                          u
                                                         in
                                                      let uu____3783 =
                                                        let uu____3784 =
                                                          let uu____3787 =
                                                            let uu____3788 =
                                                              FStar_Syntax_Util.head_and_args
                                                                u1
                                                               in
                                                            FStar_Pervasives_Native.fst
                                                              uu____3788
                                                             in
                                                          FStar_Syntax_Subst.compress
                                                            uu____3787
                                                           in
                                                        uu____3784.FStar_Syntax_Syntax.n
                                                         in
                                                      match uu____3783 with
                                                      | FStar_Syntax_Syntax.Tm_uvar
                                                          ({
                                                             FStar_Syntax_Syntax.ctx_uvar_head
                                                               = uvar;
                                                             FStar_Syntax_Syntax.ctx_uvar_gamma
                                                               = uu____3816;
                                                             FStar_Syntax_Syntax.ctx_uvar_binders
                                                               = uu____3817;
                                                             FStar_Syntax_Syntax.ctx_uvar_typ
                                                               = uu____3818;
                                                             FStar_Syntax_Syntax.ctx_uvar_reason
                                                               = uu____3819;
                                                             FStar_Syntax_Syntax.ctx_uvar_should_check
                                                               = uu____3820;
                                                             FStar_Syntax_Syntax.ctx_uvar_range
                                                               = uu____3821;_},uu____3822)
                                                          ->
                                                          bind get
                                                            (fun ps  ->
                                                               let uu____3866
                                                                 =
                                                                 uopt &&
                                                                   (uvar_free
                                                                    uvar ps)
                                                                  in
                                                               if uu____3866
                                                               then ret ()
                                                               else
                                                                 (let uu____3870
                                                                    =
                                                                    let uu____3873
                                                                    =
                                                                    let uu___123_3874
                                                                    = goal
                                                                     in
                                                                    let uu____3875
                                                                    =
                                                                    bnorm
                                                                    goal.FStar_Tactics_Types.context
                                                                    u1  in
                                                                    let uu____3876
                                                                    =
                                                                    bnorm
                                                                    goal.FStar_Tactics_Types.context
                                                                    bv.FStar_Syntax_Syntax.sort
                                                                     in
                                                                    {
                                                                    FStar_Tactics_Types.context
                                                                    =
                                                                    (uu___123_3874.FStar_Tactics_Types.context);
                                                                    FStar_Tactics_Types.witness
                                                                    =
                                                                    uu____3875;
                                                                    FStar_Tactics_Types.goal_ty
                                                                    =
                                                                    uu____3876;
                                                                    FStar_Tactics_Types.opts
                                                                    =
                                                                    (uu___123_3874.FStar_Tactics_Types.opts);
                                                                    FStar_Tactics_Types.is_guard
                                                                    = false
                                                                    }  in
                                                                    [uu____3873]
                                                                     in
                                                                  add_goals
                                                                    uu____3870))
                                                      | t -> ret ()))))))))
  
let try_unif : 'a . 'a tac -> 'a tac -> 'a tac =
  fun t  ->
    fun t'  -> mk_tac (fun ps  -> try run t ps with | NoUnif  -> run t' ps)
  
let (apply : Prims.bool -> FStar_Syntax_Syntax.term -> unit tac) =
  fun uopt  ->
    fun tm  ->
      let uu____3931 =
        mlog
          (fun uu____3936  ->
             let uu____3937 = FStar_Syntax_Print.term_to_string tm  in
             FStar_Util.print1 "apply: tm = %s\n" uu____3937)
          (fun uu____3940  ->
             let uu____3941 = cur_goal ()  in
             bind uu____3941
               (fun goal  ->
                  let uu____3947 = __tc goal.FStar_Tactics_Types.context tm
                     in
                  bind uu____3947
                    (fun uu____3969  ->
                       match uu____3969 with
                       | (tm1,typ,guard) ->
                           let typ1 =
                             bnorm goal.FStar_Tactics_Types.context typ  in
                           let uu____3982 =
                             let uu____3985 =
                               let uu____3988 = __apply uopt tm1 typ1  in
                               bind uu____3988
                                 (fun uu____3992  ->
                                    proc_guard "apply guard"
                                      goal.FStar_Tactics_Types.context guard
                                      goal.FStar_Tactics_Types.opts)
                                in
                             focus uu____3985  in
                           let uu____3993 =
                             let uu____3996 =
                               tts goal.FStar_Tactics_Types.context tm1  in
                             let uu____3997 =
                               tts goal.FStar_Tactics_Types.context typ1  in
                             let uu____3998 =
                               tts goal.FStar_Tactics_Types.context
                                 goal.FStar_Tactics_Types.goal_ty
                                in
                             fail3
                               "Cannot instantiate %s (of type %s) to match goal (%s)"
                               uu____3996 uu____3997 uu____3998
                              in
                           try_unif uu____3982 uu____3993)))
         in
      FStar_All.pipe_left (wrap_err "apply") uu____3931
  
let (lemma_or_sq :
  FStar_Syntax_Syntax.comp ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun c  ->
    let ct = FStar_Syntax_Util.comp_to_comp_typ_nouniv c  in
    let uu____4021 =
      FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
        FStar_Parser_Const.effect_Lemma_lid
       in
    if uu____4021
    then
      let uu____4028 =
        match ct.FStar_Syntax_Syntax.effect_args with
        | pre::post::uu____4047 ->
            ((FStar_Pervasives_Native.fst pre),
              (FStar_Pervasives_Native.fst post))
        | uu____4088 -> failwith "apply_lemma: impossible: not a lemma"  in
      match uu____4028 with
      | (pre,post) ->
          let post1 =
            let uu____4124 =
              let uu____4133 =
                FStar_Syntax_Syntax.as_arg FStar_Syntax_Util.exp_unit  in
              [uu____4133]  in
            FStar_Syntax_Util.mk_app post uu____4124  in
          FStar_Pervasives_Native.Some (pre, post1)
    else
      (let uu____4157 =
         FStar_Syntax_Util.is_pure_effect ct.FStar_Syntax_Syntax.effect_name
          in
       if uu____4157
       then
         let uu____4164 =
           FStar_Syntax_Util.un_squash ct.FStar_Syntax_Syntax.result_typ  in
         FStar_Util.map_opt uu____4164
           (fun post  -> (FStar_Syntax_Util.t_true, post))
       else FStar_Pervasives_Native.None)
  
let (apply_lemma : FStar_Syntax_Syntax.term -> unit tac) =
  fun tm  ->
    let uu____4197 =
      let uu____4200 =
        mlog
          (fun uu____4205  ->
             let uu____4206 = FStar_Syntax_Print.term_to_string tm  in
             FStar_Util.print1 "apply_lemma: tm = %s\n" uu____4206)
          (fun uu____4210  ->
             let is_unit_t t =
               let uu____4217 =
                 let uu____4218 = FStar_Syntax_Subst.compress t  in
                 uu____4218.FStar_Syntax_Syntax.n  in
               match uu____4217 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.unit_lid
                   -> true
               | uu____4222 -> false  in
             let uu____4223 = cur_goal ()  in
             bind uu____4223
               (fun goal  ->
                  let uu____4229 = __tc goal.FStar_Tactics_Types.context tm
                     in
                  bind uu____4229
                    (fun uu____4252  ->
                       match uu____4252 with
                       | (tm1,t,guard) ->
                           let uu____4264 =
                             FStar_Syntax_Util.arrow_formals_comp t  in
                           (match uu____4264 with
                            | (bs,comp) ->
                                let uu____4291 = lemma_or_sq comp  in
                                (match uu____4291 with
                                 | FStar_Pervasives_Native.None  ->
                                     fail "not a lemma or squashed function"
                                 | FStar_Pervasives_Native.Some (pre,post) ->
                                     let uu____4310 =
                                       FStar_List.fold_left
                                         (fun uu____4352  ->
                                            fun uu____4353  ->
                                              match (uu____4352, uu____4353)
                                              with
                                              | ((uvs,guard1,subst1),(b,aq))
                                                  ->
                                                  let b_t =
                                                    FStar_Syntax_Subst.subst
                                                      subst1
                                                      b.FStar_Syntax_Syntax.sort
                                                     in
                                                  let uu____4444 =
                                                    is_unit_t b_t  in
                                                  if uu____4444
                                                  then
                                                    (((FStar_Syntax_Util.exp_unit,
                                                        aq) :: uvs), guard1,
                                                      ((FStar_Syntax_Syntax.NT
                                                          (b,
                                                            FStar_Syntax_Util.exp_unit))
                                                      :: subst1))
                                                  else
                                                    (let uu____4480 =
                                                       FStar_TypeChecker_Util.new_implicit_var
                                                         "apply_lemma"
                                                         (goal.FStar_Tactics_Types.goal_ty).FStar_Syntax_Syntax.pos
                                                         goal.FStar_Tactics_Types.context
                                                         b_t
                                                        in
                                                     match uu____4480 with
                                                     | (u,uu____4508,g_u) ->
                                                         let uu____4522 =
                                                           FStar_TypeChecker_Rel.conj_guard
                                                             guard1 g_u
                                                            in
                                                         (((u, aq) :: uvs),
                                                           uu____4522,
                                                           ((FStar_Syntax_Syntax.NT
                                                               (b, u)) ::
                                                           subst1))))
                                         ([], guard, []) bs
                                        in
                                     (match uu____4310 with
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
                                          let uu____4583 =
                                            let uu____4586 =
                                              FStar_Syntax_Util.mk_squash
                                                FStar_Syntax_Syntax.U_zero
                                                post1
                                               in
                                            do_unify
                                              goal.FStar_Tactics_Types.context
                                              uu____4586
                                              goal.FStar_Tactics_Types.goal_ty
                                             in
                                          bind uu____4583
                                            (fun b  ->
                                               if Prims.op_Negation b
                                               then
                                                 let uu____4594 =
                                                   tts
                                                     goal.FStar_Tactics_Types.context
                                                     tm1
                                                    in
                                                 let uu____4595 =
                                                   let uu____4596 =
                                                     FStar_Syntax_Util.mk_squash
                                                       FStar_Syntax_Syntax.U_zero
                                                       post1
                                                      in
                                                   tts
                                                     goal.FStar_Tactics_Types.context
                                                     uu____4596
                                                    in
                                                 let uu____4597 =
                                                   tts
                                                     goal.FStar_Tactics_Types.context
                                                     goal.FStar_Tactics_Types.goal_ty
                                                    in
                                                 fail3
                                                   "Cannot instantiate lemma %s (with postcondition: %s) to match goal (%s)"
                                                   uu____4594 uu____4595
                                                   uu____4597
                                               else
                                                 (let uu____4599 =
                                                    add_implicits
                                                      implicits.FStar_TypeChecker_Env.implicits
                                                     in
                                                  bind uu____4599
                                                    (fun uu____4604  ->
                                                       let uu____4605 =
                                                         solve goal
                                                           FStar_Syntax_Util.exp_unit
                                                          in
                                                       bind uu____4605
                                                         (fun uu____4613  ->
                                                            let is_free_uvar
                                                              uv t1 =
                                                              let free_uvars
                                                                =
                                                                let uu____4638
                                                                  =
                                                                  let uu____4641
                                                                    =
                                                                    FStar_Syntax_Free.uvars
                                                                    t1  in
                                                                  FStar_Util.set_elements
                                                                    uu____4641
                                                                   in
                                                                FStar_List.map
                                                                  (fun x  ->
                                                                    x.FStar_Syntax_Syntax.ctx_uvar_head)
                                                                  uu____4638
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
                                                              let uu____4690
                                                                =
                                                                FStar_Syntax_Util.head_and_args
                                                                  t1
                                                                 in
                                                              match uu____4690
                                                              with
                                                              | (hd1,uu____4706)
                                                                  ->
                                                                  (match 
                                                                    hd1.FStar_Syntax_Syntax.n
                                                                   with
                                                                   | 
                                                                   FStar_Syntax_Syntax.Tm_uvar
                                                                    (uv,uu____4728)
                                                                    ->
                                                                    appears
                                                                    uv.FStar_Syntax_Syntax.ctx_uvar_head
                                                                    goals
                                                                   | 
                                                                   uu____4749
                                                                    -> false)
                                                               in
                                                            let uu____4750 =
                                                              FStar_All.pipe_right
                                                                implicits.FStar_TypeChecker_Env.implicits
                                                                (mapM
                                                                   (fun
                                                                    uu____4818
                                                                     ->
                                                                    match uu____4818
                                                                    with
                                                                    | 
                                                                    (_msg,term,ctx_uvar,_range,uu____4843)
                                                                    ->
                                                                    let uu____4844
                                                                    =
                                                                    FStar_Syntax_Util.head_and_args
                                                                    term  in
                                                                    (match uu____4844
                                                                    with
                                                                    | 
                                                                    (hd1,uu____4870)
                                                                    ->
                                                                    let env =
                                                                    let uu___126_4892
                                                                    =
                                                                    goal.FStar_Tactics_Types.context
                                                                     in
                                                                    {
                                                                    FStar_TypeChecker_Env.solver
                                                                    =
                                                                    (uu___126_4892.FStar_TypeChecker_Env.solver);
                                                                    FStar_TypeChecker_Env.range
                                                                    =
                                                                    (uu___126_4892.FStar_TypeChecker_Env.range);
                                                                    FStar_TypeChecker_Env.curmodule
                                                                    =
                                                                    (uu___126_4892.FStar_TypeChecker_Env.curmodule);
                                                                    FStar_TypeChecker_Env.gamma
                                                                    =
                                                                    (ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_gamma);
                                                                    FStar_TypeChecker_Env.gamma_sig
                                                                    =
                                                                    (uu___126_4892.FStar_TypeChecker_Env.gamma_sig);
                                                                    FStar_TypeChecker_Env.gamma_cache
                                                                    =
                                                                    (uu___126_4892.FStar_TypeChecker_Env.gamma_cache);
                                                                    FStar_TypeChecker_Env.modules
                                                                    =
                                                                    (uu___126_4892.FStar_TypeChecker_Env.modules);
                                                                    FStar_TypeChecker_Env.expected_typ
                                                                    =
                                                                    (uu___126_4892.FStar_TypeChecker_Env.expected_typ);
                                                                    FStar_TypeChecker_Env.sigtab
                                                                    =
                                                                    (uu___126_4892.FStar_TypeChecker_Env.sigtab);
                                                                    FStar_TypeChecker_Env.is_pattern
                                                                    =
                                                                    (uu___126_4892.FStar_TypeChecker_Env.is_pattern);
                                                                    FStar_TypeChecker_Env.instantiate_imp
                                                                    =
                                                                    (uu___126_4892.FStar_TypeChecker_Env.instantiate_imp);
                                                                    FStar_TypeChecker_Env.effects
                                                                    =
                                                                    (uu___126_4892.FStar_TypeChecker_Env.effects);
                                                                    FStar_TypeChecker_Env.generalize
                                                                    =
                                                                    (uu___126_4892.FStar_TypeChecker_Env.generalize);
                                                                    FStar_TypeChecker_Env.letrecs
                                                                    =
                                                                    (uu___126_4892.FStar_TypeChecker_Env.letrecs);
                                                                    FStar_TypeChecker_Env.top_level
                                                                    =
                                                                    (uu___126_4892.FStar_TypeChecker_Env.top_level);
                                                                    FStar_TypeChecker_Env.check_uvars
                                                                    =
                                                                    (uu___126_4892.FStar_TypeChecker_Env.check_uvars);
                                                                    FStar_TypeChecker_Env.use_eq
                                                                    =
                                                                    (uu___126_4892.FStar_TypeChecker_Env.use_eq);
                                                                    FStar_TypeChecker_Env.is_iface
                                                                    =
                                                                    (uu___126_4892.FStar_TypeChecker_Env.is_iface);
                                                                    FStar_TypeChecker_Env.admit
                                                                    =
                                                                    (uu___126_4892.FStar_TypeChecker_Env.admit);
                                                                    FStar_TypeChecker_Env.lax
                                                                    =
                                                                    (uu___126_4892.FStar_TypeChecker_Env.lax);
                                                                    FStar_TypeChecker_Env.lax_universes
                                                                    =
                                                                    (uu___126_4892.FStar_TypeChecker_Env.lax_universes);
                                                                    FStar_TypeChecker_Env.failhard
                                                                    =
                                                                    (uu___126_4892.FStar_TypeChecker_Env.failhard);
                                                                    FStar_TypeChecker_Env.nosynth
                                                                    =
                                                                    (uu___126_4892.FStar_TypeChecker_Env.nosynth);
                                                                    FStar_TypeChecker_Env.tc_term
                                                                    =
                                                                    (uu___126_4892.FStar_TypeChecker_Env.tc_term);
                                                                    FStar_TypeChecker_Env.type_of
                                                                    =
                                                                    (uu___126_4892.FStar_TypeChecker_Env.type_of);
                                                                    FStar_TypeChecker_Env.universe_of
                                                                    =
                                                                    (uu___126_4892.FStar_TypeChecker_Env.universe_of);
                                                                    FStar_TypeChecker_Env.check_type_of
                                                                    =
                                                                    (uu___126_4892.FStar_TypeChecker_Env.check_type_of);
                                                                    FStar_TypeChecker_Env.use_bv_sorts
                                                                    =
                                                                    (uu___126_4892.FStar_TypeChecker_Env.use_bv_sorts);
                                                                    FStar_TypeChecker_Env.qtbl_name_and_index
                                                                    =
                                                                    (uu___126_4892.FStar_TypeChecker_Env.qtbl_name_and_index);
                                                                    FStar_TypeChecker_Env.normalized_eff_names
                                                                    =
                                                                    (uu___126_4892.FStar_TypeChecker_Env.normalized_eff_names);
                                                                    FStar_TypeChecker_Env.proof_ns
                                                                    =
                                                                    (uu___126_4892.FStar_TypeChecker_Env.proof_ns);
                                                                    FStar_TypeChecker_Env.synth_hook
                                                                    =
                                                                    (uu___126_4892.FStar_TypeChecker_Env.synth_hook);
                                                                    FStar_TypeChecker_Env.splice
                                                                    =
                                                                    (uu___126_4892.FStar_TypeChecker_Env.splice);
                                                                    FStar_TypeChecker_Env.is_native_tactic
                                                                    =
                                                                    (uu___126_4892.FStar_TypeChecker_Env.is_native_tactic);
                                                                    FStar_TypeChecker_Env.identifier_info
                                                                    =
                                                                    (uu___126_4892.FStar_TypeChecker_Env.identifier_info);
                                                                    FStar_TypeChecker_Env.tc_hooks
                                                                    =
                                                                    (uu___126_4892.FStar_TypeChecker_Env.tc_hooks);
                                                                    FStar_TypeChecker_Env.dsenv
                                                                    =
                                                                    (uu___126_4892.FStar_TypeChecker_Env.dsenv);
                                                                    FStar_TypeChecker_Env.dep_graph
                                                                    =
                                                                    (uu___126_4892.FStar_TypeChecker_Env.dep_graph)
                                                                    }  in
                                                                    let uu____4893
                                                                    =
                                                                    let uu____4894
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    hd1  in
                                                                    uu____4894.FStar_Syntax_Syntax.n
                                                                     in
                                                                    (match uu____4893
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Tm_uvar
                                                                    uu____4907
                                                                    ->
                                                                    let uu____4922
                                                                    =
                                                                    let uu____4931
                                                                    =
                                                                    let uu____4934
                                                                    =
                                                                    let uu___127_4935
                                                                    = goal
                                                                     in
                                                                    let uu____4936
                                                                    =
                                                                    bnorm env
                                                                    term  in
                                                                    let uu____4937
                                                                    =
                                                                    bnorm env
                                                                    ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_typ
                                                                     in
                                                                    {
                                                                    FStar_Tactics_Types.context
                                                                    = env;
                                                                    FStar_Tactics_Types.witness
                                                                    =
                                                                    uu____4936;
                                                                    FStar_Tactics_Types.goal_ty
                                                                    =
                                                                    uu____4937;
                                                                    FStar_Tactics_Types.opts
                                                                    =
                                                                    (uu___127_4935.FStar_Tactics_Types.opts);
                                                                    FStar_Tactics_Types.is_guard
                                                                    =
                                                                    (uu___127_4935.FStar_Tactics_Types.is_guard)
                                                                    }  in
                                                                    [uu____4934]
                                                                     in
                                                                    (uu____4931,
                                                                    [])  in
                                                                    ret
                                                                    uu____4922
                                                                    | 
                                                                    uu____4950
                                                                    ->
                                                                    let g_typ
                                                                    =
                                                                    let uu____4952
                                                                    =
                                                                    FStar_Options.__temp_fast_implicits
                                                                    ()  in
                                                                    if
                                                                    uu____4952
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
                                                                    let uu____4955
                                                                    =
                                                                    let uu____4962
                                                                    =
                                                                    FStar_TypeChecker_Env.set_expected_typ
                                                                    env
                                                                    ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_typ
                                                                     in
                                                                    env.FStar_TypeChecker_Env.type_of
                                                                    uu____4962
                                                                    term1  in
                                                                    match uu____4955
                                                                    with
                                                                    | 
                                                                    (uu____4963,uu____4964,g_typ)
                                                                    -> g_typ)
                                                                     in
                                                                    let uu____4966
                                                                    =
                                                                    goal_from_guard
                                                                    "apply_lemma solved arg"
                                                                    goal.FStar_Tactics_Types.context
                                                                    g_typ
                                                                    goal.FStar_Tactics_Types.opts
                                                                     in
                                                                    bind
                                                                    uu____4966
                                                                    (fun
                                                                    uu___90_4982
                                                                     ->
                                                                    match uu___90_4982
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
                                                            bind uu____4750
                                                              (fun goals_  ->
                                                                 let sub_goals
                                                                   =
                                                                   let uu____5050
                                                                    =
                                                                    FStar_List.map
                                                                    FStar_Pervasives_Native.fst
                                                                    goals_
                                                                     in
                                                                   FStar_List.flatten
                                                                    uu____5050
                                                                    in
                                                                 let smt_goals
                                                                   =
                                                                   let uu____5072
                                                                    =
                                                                    FStar_List.map
                                                                    FStar_Pervasives_Native.snd
                                                                    goals_
                                                                     in
                                                                   FStar_List.flatten
                                                                    uu____5072
                                                                    in
                                                                 let rec filter'
                                                                   f xs =
                                                                   match xs
                                                                   with
                                                                   | 
                                                                   [] -> []
                                                                   | 
                                                                   x::xs1 ->
                                                                    let uu____5133
                                                                    = f x xs1
                                                                     in
                                                                    if
                                                                    uu____5133
                                                                    then
                                                                    let uu____5136
                                                                    =
                                                                    filter' f
                                                                    xs1  in x
                                                                    ::
                                                                    uu____5136
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
                                                                    let uu____5150
                                                                    =
                                                                    checkone
                                                                    g.FStar_Tactics_Types.witness
                                                                    goals  in
                                                                    Prims.op_Negation
                                                                    uu____5150)
                                                                    sub_goals
                                                                    in
                                                                 let uu____5151
                                                                   =
                                                                   proc_guard
                                                                    "apply_lemma guard"
                                                                    goal.FStar_Tactics_Types.context
                                                                    guard
                                                                    goal.FStar_Tactics_Types.opts
                                                                    in
                                                                 bind
                                                                   uu____5151
                                                                   (fun
                                                                    uu____5156
                                                                     ->
                                                                    let uu____5157
                                                                    =
                                                                    let uu____5160
                                                                    =
                                                                    let uu____5161
                                                                    =
                                                                    let uu____5162
                                                                    =
                                                                    FStar_Syntax_Util.mk_squash
                                                                    FStar_Syntax_Syntax.U_zero
                                                                    pre1  in
                                                                    istrivial
                                                                    goal.FStar_Tactics_Types.context
                                                                    uu____5162
                                                                     in
                                                                    Prims.op_Negation
                                                                    uu____5161
                                                                     in
                                                                    if
                                                                    uu____5160
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
                                                                    uu____5157
                                                                    (fun
                                                                    uu____5168
                                                                     ->
                                                                    let uu____5169
                                                                    =
                                                                    add_smt_goals
                                                                    smt_goals
                                                                     in
                                                                    bind
                                                                    uu____5169
                                                                    (fun
                                                                    uu____5173
                                                                     ->
                                                                    add_goals
                                                                    sub_goals1))))))))))))))
         in
      focus uu____4200  in
    FStar_All.pipe_left (wrap_err "apply_lemma") uu____4197
  
let (destruct_eq' :
  FStar_Reflection_Data.typ ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun typ  ->
    let uu____5195 = FStar_Syntax_Util.destruct_typ_as_formula typ  in
    match uu____5195 with
    | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn
        (l,uu____5205::(e1,uu____5207)::(e2,uu____5209)::[])) when
        FStar_Ident.lid_equals l FStar_Parser_Const.eq2_lid ->
        FStar_Pervasives_Native.Some (e1, e2)
    | uu____5252 -> FStar_Pervasives_Native.None
  
let (destruct_eq :
  FStar_Reflection_Data.typ ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun typ  ->
    let uu____5276 = destruct_eq' typ  in
    match uu____5276 with
    | FStar_Pervasives_Native.Some t -> FStar_Pervasives_Native.Some t
    | FStar_Pervasives_Native.None  ->
        let uu____5306 = FStar_Syntax_Util.un_squash typ  in
        (match uu____5306 with
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
        let uu____5368 = FStar_TypeChecker_Env.pop_bv e1  in
        match uu____5368 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (bv',e') ->
            if FStar_Syntax_Syntax.bv_eq bvar bv'
            then FStar_Pervasives_Native.Some (e', [])
            else
              (let uu____5416 = aux e'  in
               FStar_Util.map_opt uu____5416
                 (fun uu____5440  ->
                    match uu____5440 with | (e'',bvs) -> (e'', (bv' :: bvs))))
         in
      let uu____5461 = aux e  in
      FStar_Util.map_opt uu____5461
        (fun uu____5485  ->
           match uu____5485 with | (e',bvs) -> (e', (FStar_List.rev bvs)))
  
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
          let uu____5552 = split_env b1 g.FStar_Tactics_Types.context  in
          FStar_Util.map_opt uu____5552
            (fun uu____5576  ->
               match uu____5576 with
               | (e0,bvs) ->
                   let s1 bv =
                     let uu___128_5595 = bv  in
                     let uu____5596 =
                       FStar_Syntax_Subst.subst s bv.FStar_Syntax_Syntax.sort
                        in
                     {
                       FStar_Syntax_Syntax.ppname =
                         (uu___128_5595.FStar_Syntax_Syntax.ppname);
                       FStar_Syntax_Syntax.index =
                         (uu___128_5595.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort = uu____5596
                     }  in
                   let bvs1 = FStar_List.map s1 bvs  in
                   let c = push_bvs e0 (b2 :: bvs1)  in
                   let w =
                     FStar_Syntax_Subst.subst s g.FStar_Tactics_Types.witness
                      in
                   let t =
                     FStar_Syntax_Subst.subst s g.FStar_Tactics_Types.goal_ty
                      in
                   let uu___129_5605 = g  in
                   {
                     FStar_Tactics_Types.context = c;
                     FStar_Tactics_Types.witness = w;
                     FStar_Tactics_Types.goal_ty = t;
                     FStar_Tactics_Types.opts =
                       (uu___129_5605.FStar_Tactics_Types.opts);
                     FStar_Tactics_Types.is_guard =
                       (uu___129_5605.FStar_Tactics_Types.is_guard)
                   })
  
let (rewrite : FStar_Syntax_Syntax.binder -> unit tac) =
  fun h  ->
    let uu____5615 = cur_goal ()  in
    bind uu____5615
      (fun goal  ->
         let uu____5623 = h  in
         match uu____5623 with
         | (bv,uu____5627) ->
             mlog
               (fun uu____5631  ->
                  let uu____5632 = FStar_Syntax_Print.bv_to_string bv  in
                  let uu____5633 =
                    tts goal.FStar_Tactics_Types.context
                      bv.FStar_Syntax_Syntax.sort
                     in
                  FStar_Util.print2 "+++Rewrite %s : %s\n" uu____5632
                    uu____5633)
               (fun uu____5636  ->
                  let uu____5637 =
                    split_env bv goal.FStar_Tactics_Types.context  in
                  match uu____5637 with
                  | FStar_Pervasives_Native.None  ->
                      fail "rewrite: binder not found in environment"
                  | FStar_Pervasives_Native.Some (e0,bvs) ->
                      let uu____5666 =
                        destruct_eq bv.FStar_Syntax_Syntax.sort  in
                      (match uu____5666 with
                       | FStar_Pervasives_Native.Some (x,e) ->
                           let uu____5681 =
                             let uu____5682 = FStar_Syntax_Subst.compress x
                                in
                             uu____5682.FStar_Syntax_Syntax.n  in
                           (match uu____5681 with
                            | FStar_Syntax_Syntax.Tm_name x1 ->
                                let s = [FStar_Syntax_Syntax.NT (x1, e)]  in
                                let s1 bv1 =
                                  let uu___130_5699 = bv1  in
                                  let uu____5700 =
                                    FStar_Syntax_Subst.subst s
                                      bv1.FStar_Syntax_Syntax.sort
                                     in
                                  {
                                    FStar_Syntax_Syntax.ppname =
                                      (uu___130_5699.FStar_Syntax_Syntax.ppname);
                                    FStar_Syntax_Syntax.index =
                                      (uu___130_5699.FStar_Syntax_Syntax.index);
                                    FStar_Syntax_Syntax.sort = uu____5700
                                  }  in
                                let bvs1 = FStar_List.map s1 bvs  in
                                let uu____5706 =
                                  let uu___131_5707 = goal  in
                                  let uu____5708 = push_bvs e0 (bv :: bvs1)
                                     in
                                  let uu____5709 =
                                    FStar_Syntax_Subst.subst s
                                      goal.FStar_Tactics_Types.witness
                                     in
                                  let uu____5710 =
                                    FStar_Syntax_Subst.subst s
                                      goal.FStar_Tactics_Types.goal_ty
                                     in
                                  {
                                    FStar_Tactics_Types.context = uu____5708;
                                    FStar_Tactics_Types.witness = uu____5709;
                                    FStar_Tactics_Types.goal_ty = uu____5710;
                                    FStar_Tactics_Types.opts =
                                      (uu___131_5707.FStar_Tactics_Types.opts);
                                    FStar_Tactics_Types.is_guard =
                                      (uu___131_5707.FStar_Tactics_Types.is_guard)
                                  }  in
                                replace_cur uu____5706
                            | uu____5711 ->
                                fail
                                  "rewrite: Not an equality hypothesis with a variable on the LHS")
                       | uu____5712 ->
                           fail "rewrite: Not an equality hypothesis")))
  
let (rename_to : FStar_Syntax_Syntax.binder -> Prims.string -> unit tac) =
  fun b  ->
    fun s  ->
      let uu____5733 = cur_goal ()  in
      bind uu____5733
        (fun goal  ->
           let uu____5744 = b  in
           match uu____5744 with
           | (bv,uu____5748) ->
               let bv' =
                 let uu____5750 =
                   let uu___132_5751 = bv  in
                   let uu____5752 =
                     FStar_Ident.mk_ident
                       (s,
                         ((bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))
                      in
                   {
                     FStar_Syntax_Syntax.ppname = uu____5752;
                     FStar_Syntax_Syntax.index =
                       (uu___132_5751.FStar_Syntax_Syntax.index);
                     FStar_Syntax_Syntax.sort =
                       (uu___132_5751.FStar_Syntax_Syntax.sort)
                   }  in
                 FStar_Syntax_Syntax.freshen_bv uu____5750  in
               let s1 =
                 let uu____5756 =
                   let uu____5757 =
                     let uu____5764 = FStar_Syntax_Syntax.bv_to_name bv'  in
                     (bv, uu____5764)  in
                   FStar_Syntax_Syntax.NT uu____5757  in
                 [uu____5756]  in
               let uu____5769 = subst_goal bv bv' s1 goal  in
               (match uu____5769 with
                | FStar_Pervasives_Native.None  ->
                    fail "rename_to: binder not found in environment"
                | FStar_Pervasives_Native.Some goal1 -> replace_cur goal1))
  
let (binder_retype : FStar_Syntax_Syntax.binder -> unit tac) =
  fun b  ->
    let uu____5784 = cur_goal ()  in
    bind uu____5784
      (fun goal  ->
         let uu____5793 = b  in
         match uu____5793 with
         | (bv,uu____5797) ->
             let uu____5798 = split_env bv goal.FStar_Tactics_Types.context
                in
             (match uu____5798 with
              | FStar_Pervasives_Native.None  ->
                  fail "binder_retype: binder is not present in environment"
              | FStar_Pervasives_Native.Some (e0,bvs) ->
                  let uu____5827 = FStar_Syntax_Util.type_u ()  in
                  (match uu____5827 with
                   | (ty,u) ->
                       let uu____5836 = new_uvar "binder_retype" e0 ty  in
                       bind uu____5836
                         (fun t'  ->
                            let bv'' =
                              let uu___133_5846 = bv  in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___133_5846.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___133_5846.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = t'
                              }  in
                            let s =
                              let uu____5850 =
                                let uu____5851 =
                                  let uu____5858 =
                                    FStar_Syntax_Syntax.bv_to_name bv''  in
                                  (bv, uu____5858)  in
                                FStar_Syntax_Syntax.NT uu____5851  in
                              [uu____5850]  in
                            let bvs1 =
                              FStar_List.map
                                (fun b1  ->
                                   let uu___134_5870 = b1  in
                                   let uu____5871 =
                                     FStar_Syntax_Subst.subst s
                                       b1.FStar_Syntax_Syntax.sort
                                      in
                                   {
                                     FStar_Syntax_Syntax.ppname =
                                       (uu___134_5870.FStar_Syntax_Syntax.ppname);
                                     FStar_Syntax_Syntax.index =
                                       (uu___134_5870.FStar_Syntax_Syntax.index);
                                     FStar_Syntax_Syntax.sort = uu____5871
                                   }) bvs
                               in
                            let env' = push_bvs e0 (bv'' :: bvs1)  in
                            bind __dismiss
                              (fun uu____5877  ->
                                 let uu____5878 =
                                   let uu____5881 =
                                     let uu____5884 =
                                       let uu___135_5885 = goal  in
                                       let uu____5886 =
                                         FStar_Syntax_Subst.subst s
                                           goal.FStar_Tactics_Types.witness
                                          in
                                       let uu____5887 =
                                         FStar_Syntax_Subst.subst s
                                           goal.FStar_Tactics_Types.goal_ty
                                          in
                                       {
                                         FStar_Tactics_Types.context = env';
                                         FStar_Tactics_Types.witness =
                                           uu____5886;
                                         FStar_Tactics_Types.goal_ty =
                                           uu____5887;
                                         FStar_Tactics_Types.opts =
                                           (uu___135_5885.FStar_Tactics_Types.opts);
                                         FStar_Tactics_Types.is_guard =
                                           (uu___135_5885.FStar_Tactics_Types.is_guard)
                                       }  in
                                     [uu____5884]  in
                                   add_goals uu____5881  in
                                 bind uu____5878
                                   (fun uu____5890  ->
                                      let uu____5891 =
                                        FStar_Syntax_Util.mk_eq2
                                          (FStar_Syntax_Syntax.U_succ u) ty
                                          bv.FStar_Syntax_Syntax.sort t'
                                         in
                                      add_irrelevant_goal
                                        "binder_retype equation" e0
                                        uu____5891
                                        goal.FStar_Tactics_Types.opts))))))
  
let (norm_binder_type :
  FStar_Syntax_Embeddings.norm_step Prims.list ->
    FStar_Syntax_Syntax.binder -> unit tac)
  =
  fun s  ->
    fun b  ->
      let uu____5910 = cur_goal ()  in
      bind uu____5910
        (fun goal  ->
           let uu____5919 = b  in
           match uu____5919 with
           | (bv,uu____5923) ->
               let uu____5924 = split_env bv goal.FStar_Tactics_Types.context
                  in
               (match uu____5924 with
                | FStar_Pervasives_Native.None  ->
                    fail
                      "binder_retype: binder is not present in environment"
                | FStar_Pervasives_Native.Some (e0,bvs) ->
                    let steps =
                      let uu____5956 =
                        FStar_TypeChecker_Normalize.tr_norm_steps s  in
                      FStar_List.append
                        [FStar_TypeChecker_Normalize.Reify;
                        FStar_TypeChecker_Normalize.UnfoldTac] uu____5956
                       in
                    let sort' =
                      normalize steps e0 bv.FStar_Syntax_Syntax.sort  in
                    let bv' =
                      let uu___136_5961 = bv  in
                      {
                        FStar_Syntax_Syntax.ppname =
                          (uu___136_5961.FStar_Syntax_Syntax.ppname);
                        FStar_Syntax_Syntax.index =
                          (uu___136_5961.FStar_Syntax_Syntax.index);
                        FStar_Syntax_Syntax.sort = sort'
                      }  in
                    let env' = push_bvs e0 (bv' :: bvs)  in
                    replace_cur
                      (let uu___137_5965 = goal  in
                       {
                         FStar_Tactics_Types.context = env';
                         FStar_Tactics_Types.witness =
                           (uu___137_5965.FStar_Tactics_Types.witness);
                         FStar_Tactics_Types.goal_ty =
                           (uu___137_5965.FStar_Tactics_Types.goal_ty);
                         FStar_Tactics_Types.opts =
                           (uu___137_5965.FStar_Tactics_Types.opts);
                         FStar_Tactics_Types.is_guard =
                           (uu___137_5965.FStar_Tactics_Types.is_guard)
                       })))
  
let (revert : unit -> unit tac) =
  fun uu____5972  ->
    let uu____5975 = cur_goal ()  in
    bind uu____5975
      (fun goal  ->
         let uu____5981 =
           FStar_TypeChecker_Env.pop_bv goal.FStar_Tactics_Types.context  in
         match uu____5981 with
         | FStar_Pervasives_Native.None  ->
             fail "Cannot revert; empty context"
         | FStar_Pervasives_Native.Some (x,env') ->
             let typ' =
               let uu____6003 =
                 FStar_Syntax_Syntax.mk_Total
                   goal.FStar_Tactics_Types.goal_ty
                  in
               FStar_Syntax_Util.arrow [(x, FStar_Pervasives_Native.None)]
                 uu____6003
                in
             let w' =
               FStar_Syntax_Util.abs [(x, FStar_Pervasives_Native.None)]
                 goal.FStar_Tactics_Types.witness
                 FStar_Pervasives_Native.None
                in
             replace_cur
               (let uu___138_6027 = goal  in
                {
                  FStar_Tactics_Types.context = env';
                  FStar_Tactics_Types.witness = w';
                  FStar_Tactics_Types.goal_ty = typ';
                  FStar_Tactics_Types.opts =
                    (uu___138_6027.FStar_Tactics_Types.opts);
                  FStar_Tactics_Types.is_guard =
                    (uu___138_6027.FStar_Tactics_Types.is_guard)
                }))
  
let (free_in :
  FStar_Syntax_Syntax.bv -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun bv  ->
    fun t  ->
      let uu____6038 = FStar_Syntax_Free.names t  in
      FStar_Util.set_mem bv uu____6038
  
let rec (clear : FStar_Syntax_Syntax.binder -> unit tac) =
  fun b  ->
    let bv = FStar_Pervasives_Native.fst b  in
    let uu____6051 = cur_goal ()  in
    bind uu____6051
      (fun goal  ->
         mlog
           (fun uu____6059  ->
              let uu____6060 = FStar_Syntax_Print.binder_to_string b  in
              let uu____6061 =
                let uu____6062 =
                  let uu____6063 =
                    FStar_TypeChecker_Env.all_binders
                      goal.FStar_Tactics_Types.context
                     in
                  FStar_All.pipe_right uu____6063 FStar_List.length  in
                FStar_All.pipe_right uu____6062 FStar_Util.string_of_int  in
              FStar_Util.print2 "Clear of (%s), env has %s binders\n"
                uu____6060 uu____6061)
           (fun uu____6082  ->
              let uu____6083 = split_env bv goal.FStar_Tactics_Types.context
                 in
              match uu____6083 with
              | FStar_Pervasives_Native.None  ->
                  fail "Cannot clear; binder not in environment"
              | FStar_Pervasives_Native.Some (e',bvs) ->
                  let rec check1 bvs1 =
                    match bvs1 with
                    | [] -> ret ()
                    | bv'::bvs2 ->
                        let uu____6130 =
                          free_in bv bv'.FStar_Syntax_Syntax.sort  in
                        if uu____6130
                        then
                          let uu____6133 =
                            let uu____6134 =
                              FStar_Syntax_Print.bv_to_string bv'  in
                            FStar_Util.format1
                              "Cannot clear; binder present in the type of %s"
                              uu____6134
                             in
                          fail uu____6133
                        else check1 bvs2
                     in
                  let uu____6136 =
                    free_in bv goal.FStar_Tactics_Types.goal_ty  in
                  if uu____6136
                  then fail "Cannot clear; binder present in goal"
                  else
                    (let uu____6140 = check1 bvs  in
                     bind uu____6140
                       (fun uu____6146  ->
                          let env' = push_bvs e' bvs  in
                          let uu____6148 =
                            new_uvar "clear.witness" env'
                              goal.FStar_Tactics_Types.goal_ty
                             in
                          bind uu____6148
                            (fun ut  ->
                               let uu____6154 =
                                 do_unify goal.FStar_Tactics_Types.context
                                   goal.FStar_Tactics_Types.witness ut
                                  in
                               bind uu____6154
                                 (fun b1  ->
                                    if b1
                                    then
                                      replace_cur
                                        (let uu___139_6163 = goal  in
                                         {
                                           FStar_Tactics_Types.context = env';
                                           FStar_Tactics_Types.witness = ut;
                                           FStar_Tactics_Types.goal_ty =
                                             (uu___139_6163.FStar_Tactics_Types.goal_ty);
                                           FStar_Tactics_Types.opts =
                                             (uu___139_6163.FStar_Tactics_Types.opts);
                                           FStar_Tactics_Types.is_guard =
                                             (uu___139_6163.FStar_Tactics_Types.is_guard)
                                         })
                                    else
                                      fail
                                        "Cannot clear; binder appears in witness"))))))
  
let (clear_top : unit -> unit tac) =
  fun uu____6171  ->
    let uu____6174 = cur_goal ()  in
    bind uu____6174
      (fun goal  ->
         let uu____6180 =
           FStar_TypeChecker_Env.pop_bv goal.FStar_Tactics_Types.context  in
         match uu____6180 with
         | FStar_Pervasives_Native.None  ->
             fail "Cannot clear; empty context"
         | FStar_Pervasives_Native.Some (x,uu____6194) ->
             let uu____6199 = FStar_Syntax_Syntax.mk_binder x  in
             clear uu____6199)
  
let (prune : Prims.string -> unit tac) =
  fun s  ->
    let uu____6209 = cur_goal ()  in
    bind uu____6209
      (fun g  ->
         let ctx = g.FStar_Tactics_Types.context  in
         let ctx' =
           let uu____6219 = FStar_Ident.path_of_text s  in
           FStar_TypeChecker_Env.rem_proof_ns ctx uu____6219  in
         let g' =
           let uu___140_6221 = g  in
           {
             FStar_Tactics_Types.context = ctx';
             FStar_Tactics_Types.witness =
               (uu___140_6221.FStar_Tactics_Types.witness);
             FStar_Tactics_Types.goal_ty =
               (uu___140_6221.FStar_Tactics_Types.goal_ty);
             FStar_Tactics_Types.opts =
               (uu___140_6221.FStar_Tactics_Types.opts);
             FStar_Tactics_Types.is_guard =
               (uu___140_6221.FStar_Tactics_Types.is_guard)
           }  in
         bind __dismiss (fun uu____6223  -> add_goals [g']))
  
let (addns : Prims.string -> unit tac) =
  fun s  ->
    let uu____6233 = cur_goal ()  in
    bind uu____6233
      (fun g  ->
         let ctx = g.FStar_Tactics_Types.context  in
         let ctx' =
           let uu____6243 = FStar_Ident.path_of_text s  in
           FStar_TypeChecker_Env.add_proof_ns ctx uu____6243  in
         let g' =
           let uu___141_6245 = g  in
           {
             FStar_Tactics_Types.context = ctx';
             FStar_Tactics_Types.witness =
               (uu___141_6245.FStar_Tactics_Types.witness);
             FStar_Tactics_Types.goal_ty =
               (uu___141_6245.FStar_Tactics_Types.goal_ty);
             FStar_Tactics_Types.opts =
               (uu___141_6245.FStar_Tactics_Types.opts);
             FStar_Tactics_Types.is_guard =
               (uu___141_6245.FStar_Tactics_Types.is_guard)
           }  in
         bind __dismiss (fun uu____6247  -> add_goals [g']))
  
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
            let uu____6287 = FStar_Syntax_Subst.compress t  in
            uu____6287.FStar_Syntax_Syntax.n  in
          let uu____6290 =
            if d = FStar_Tactics_Types.TopDown
            then
              f env
                (let uu___145_6296 = t  in
                 {
                   FStar_Syntax_Syntax.n = tn;
                   FStar_Syntax_Syntax.pos =
                     (uu___145_6296.FStar_Syntax_Syntax.pos);
                   FStar_Syntax_Syntax.vars =
                     (uu___145_6296.FStar_Syntax_Syntax.vars)
                 })
            else ret t  in
          bind uu____6290
            (fun t1  ->
               let ff = tac_fold_env d f env  in
               let tn1 =
                 let uu____6312 =
                   let uu____6313 = FStar_Syntax_Subst.compress t1  in
                   uu____6313.FStar_Syntax_Syntax.n  in
                 match uu____6312 with
                 | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
                     let uu____6340 = ff hd1  in
                     bind uu____6340
                       (fun hd2  ->
                          let fa uu____6362 =
                            match uu____6362 with
                            | (a,q) ->
                                let uu____6375 = ff a  in
                                bind uu____6375 (fun a1  -> ret (a1, q))
                             in
                          let uu____6388 = mapM fa args  in
                          bind uu____6388
                            (fun args1  ->
                               ret (FStar_Syntax_Syntax.Tm_app (hd2, args1))))
                 | FStar_Syntax_Syntax.Tm_abs (bs,t2,k) ->
                     let uu____6454 = FStar_Syntax_Subst.open_term bs t2  in
                     (match uu____6454 with
                      | (bs1,t') ->
                          let uu____6463 =
                            let uu____6466 =
                              FStar_TypeChecker_Env.push_binders env bs1  in
                            tac_fold_env d f uu____6466 t'  in
                          bind uu____6463
                            (fun t''  ->
                               let uu____6470 =
                                 let uu____6471 =
                                   let uu____6488 =
                                     FStar_Syntax_Subst.close_binders bs1  in
                                   let uu____6495 =
                                     FStar_Syntax_Subst.close bs1 t''  in
                                   (uu____6488, uu____6495, k)  in
                                 FStar_Syntax_Syntax.Tm_abs uu____6471  in
                               ret uu____6470))
                 | FStar_Syntax_Syntax.Tm_arrow (bs,k) -> ret tn
                 | FStar_Syntax_Syntax.Tm_match (hd1,brs) ->
                     let uu____6564 = ff hd1  in
                     bind uu____6564
                       (fun hd2  ->
                          let ffb br =
                            let uu____6579 =
                              FStar_Syntax_Subst.open_branch br  in
                            match uu____6579 with
                            | (pat,w,e) ->
                                let bvs = FStar_Syntax_Syntax.pat_bvs pat  in
                                let ff1 =
                                  let uu____6611 =
                                    FStar_TypeChecker_Env.push_bvs env bvs
                                     in
                                  tac_fold_env d f uu____6611  in
                                let uu____6612 = ff1 e  in
                                bind uu____6612
                                  (fun e1  ->
                                     let br1 =
                                       FStar_Syntax_Subst.close_branch
                                         (pat, w, e1)
                                        in
                                     ret br1)
                             in
                          let uu____6627 = mapM ffb brs  in
                          bind uu____6627
                            (fun brs1  ->
                               ret (FStar_Syntax_Syntax.Tm_match (hd2, brs1))))
                 | FStar_Syntax_Syntax.Tm_let
                     ((false
                       ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl bv;
                          FStar_Syntax_Syntax.lbunivs = uu____6671;
                          FStar_Syntax_Syntax.lbtyp = uu____6672;
                          FStar_Syntax_Syntax.lbeff = uu____6673;
                          FStar_Syntax_Syntax.lbdef = def;
                          FStar_Syntax_Syntax.lbattrs = uu____6675;
                          FStar_Syntax_Syntax.lbpos = uu____6676;_}::[]),e)
                     ->
                     let lb =
                       let uu____6701 =
                         let uu____6702 = FStar_Syntax_Subst.compress t1  in
                         uu____6702.FStar_Syntax_Syntax.n  in
                       match uu____6701 with
                       | FStar_Syntax_Syntax.Tm_let
                           ((false ,lb::[]),uu____6706) -> lb
                       | uu____6719 -> failwith "impossible"  in
                     let fflb lb1 =
                       let uu____6728 = ff lb1.FStar_Syntax_Syntax.lbdef  in
                       bind uu____6728
                         (fun def1  ->
                            ret
                              (let uu___142_6734 = lb1  in
                               {
                                 FStar_Syntax_Syntax.lbname =
                                   (uu___142_6734.FStar_Syntax_Syntax.lbname);
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___142_6734.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp =
                                   (uu___142_6734.FStar_Syntax_Syntax.lbtyp);
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___142_6734.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def1;
                                 FStar_Syntax_Syntax.lbattrs =
                                   (uu___142_6734.FStar_Syntax_Syntax.lbattrs);
                                 FStar_Syntax_Syntax.lbpos =
                                   (uu___142_6734.FStar_Syntax_Syntax.lbpos)
                               }))
                        in
                     let uu____6735 = fflb lb  in
                     bind uu____6735
                       (fun lb1  ->
                          let uu____6745 =
                            let uu____6750 =
                              let uu____6751 =
                                FStar_Syntax_Syntax.mk_binder bv  in
                              [uu____6751]  in
                            FStar_Syntax_Subst.open_term uu____6750 e  in
                          match uu____6745 with
                          | (bs,e1) ->
                              let ff1 =
                                let uu____6775 =
                                  FStar_TypeChecker_Env.push_binders env bs
                                   in
                                tac_fold_env d f uu____6775  in
                              let uu____6776 = ff1 e1  in
                              bind uu____6776
                                (fun e2  ->
                                   let e3 = FStar_Syntax_Subst.close bs e2
                                      in
                                   ret
                                     (FStar_Syntax_Syntax.Tm_let
                                        ((false, [lb1]), e3))))
                 | FStar_Syntax_Syntax.Tm_let ((true ,lbs),e) ->
                     let fflb lb =
                       let uu____6817 = ff lb.FStar_Syntax_Syntax.lbdef  in
                       bind uu____6817
                         (fun def  ->
                            ret
                              (let uu___143_6823 = lb  in
                               {
                                 FStar_Syntax_Syntax.lbname =
                                   (uu___143_6823.FStar_Syntax_Syntax.lbname);
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___143_6823.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp =
                                   (uu___143_6823.FStar_Syntax_Syntax.lbtyp);
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___143_6823.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def;
                                 FStar_Syntax_Syntax.lbattrs =
                                   (uu___143_6823.FStar_Syntax_Syntax.lbattrs);
                                 FStar_Syntax_Syntax.lbpos =
                                   (uu___143_6823.FStar_Syntax_Syntax.lbpos)
                               }))
                        in
                     let uu____6824 = FStar_Syntax_Subst.open_let_rec lbs e
                        in
                     (match uu____6824 with
                      | (lbs1,e1) ->
                          let uu____6839 = mapM fflb lbs1  in
                          bind uu____6839
                            (fun lbs2  ->
                               let uu____6851 = ff e1  in
                               bind uu____6851
                                 (fun e2  ->
                                    let uu____6859 =
                                      FStar_Syntax_Subst.close_let_rec lbs2
                                        e2
                                       in
                                    match uu____6859 with
                                    | (lbs3,e3) ->
                                        ret
                                          (FStar_Syntax_Syntax.Tm_let
                                             ((true, lbs3), e3)))))
                 | FStar_Syntax_Syntax.Tm_ascribed (t2,asc,eff) ->
                     let uu____6927 = ff t2  in
                     bind uu____6927
                       (fun t3  ->
                          ret
                            (FStar_Syntax_Syntax.Tm_ascribed (t3, asc, eff)))
                 | FStar_Syntax_Syntax.Tm_meta (t2,m) ->
                     let uu____6958 = ff t2  in
                     bind uu____6958
                       (fun t3  -> ret (FStar_Syntax_Syntax.Tm_meta (t3, m)))
                 | uu____6965 -> ret tn  in
               bind tn1
                 (fun tn2  ->
                    let t' =
                      let uu___144_6972 = t1  in
                      {
                        FStar_Syntax_Syntax.n = tn2;
                        FStar_Syntax_Syntax.pos =
                          (uu___144_6972.FStar_Syntax_Syntax.pos);
                        FStar_Syntax_Syntax.vars =
                          (uu___144_6972.FStar_Syntax_Syntax.vars)
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
            let uu____7009 = FStar_TypeChecker_TcTerm.tc_term env t  in
            match uu____7009 with
            | (t1,lcomp,g) ->
                let uu____7021 =
                  (let uu____7024 =
                     FStar_Syntax_Util.is_pure_or_ghost_lcomp lcomp  in
                   Prims.op_Negation uu____7024) ||
                    (let uu____7026 = FStar_TypeChecker_Rel.is_trivial g  in
                     Prims.op_Negation uu____7026)
                   in
                if uu____7021
                then ret t1
                else
                  (let rewrite_eq =
                     let typ = lcomp.FStar_Syntax_Syntax.res_typ  in
                     let uu____7036 = new_uvar "pointwise_rec" env typ  in
                     bind uu____7036
                       (fun ut  ->
                          log ps
                            (fun uu____7047  ->
                               let uu____7048 =
                                 FStar_Syntax_Print.term_to_string t1  in
                               let uu____7049 =
                                 FStar_Syntax_Print.term_to_string ut  in
                               FStar_Util.print2
                                 "Pointwise_rec: making equality\n\t%s ==\n\t%s\n"
                                 uu____7048 uu____7049);
                          (let uu____7050 =
                             let uu____7053 =
                               let uu____7054 =
                                 FStar_TypeChecker_TcTerm.universe_of env typ
                                  in
                               FStar_Syntax_Util.mk_eq2 uu____7054 typ t1 ut
                                in
                             add_irrelevant_goal "pointwise_rec equation" env
                               uu____7053 opts
                              in
                           bind uu____7050
                             (fun uu____7057  ->
                                let uu____7058 =
                                  bind tau
                                    (fun uu____7064  ->
                                       let ut1 =
                                         FStar_TypeChecker_Normalize.reduce_uvar_solutions
                                           env ut
                                          in
                                       log ps
                                         (fun uu____7070  ->
                                            let uu____7071 =
                                              FStar_Syntax_Print.term_to_string
                                                t1
                                               in
                                            let uu____7072 =
                                              FStar_Syntax_Print.term_to_string
                                                ut1
                                               in
                                            FStar_Util.print2
                                              "Pointwise_rec: succeeded rewriting\n\t%s to\n\t%s\n"
                                              uu____7071 uu____7072);
                                       ret ut1)
                                   in
                                focus uu____7058)))
                      in
                   let uu____7073 = trytac' rewrite_eq  in
                   bind uu____7073
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
          let uu____7271 = FStar_Syntax_Subst.compress t  in
          maybe_continue ctrl uu____7271
            (fun t1  ->
               let uu____7279 =
                 f env
                   (let uu___148_7288 = t1  in
                    {
                      FStar_Syntax_Syntax.n = (t1.FStar_Syntax_Syntax.n);
                      FStar_Syntax_Syntax.pos =
                        (uu___148_7288.FStar_Syntax_Syntax.pos);
                      FStar_Syntax_Syntax.vars =
                        (uu___148_7288.FStar_Syntax_Syntax.vars)
                    })
                  in
               bind uu____7279
                 (fun uu____7304  ->
                    match uu____7304 with
                    | (t2,ctrl1) ->
                        maybe_continue ctrl1 t2
                          (fun t3  ->
                             let uu____7327 =
                               let uu____7328 =
                                 FStar_Syntax_Subst.compress t3  in
                               uu____7328.FStar_Syntax_Syntax.n  in
                             match uu____7327 with
                             | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
                                 let uu____7361 =
                                   ctrl_tac_fold f env ctrl1 hd1  in
                                 bind uu____7361
                                   (fun uu____7386  ->
                                      match uu____7386 with
                                      | (hd2,ctrl2) ->
                                          let ctrl3 = keep_going ctrl2  in
                                          let uu____7402 =
                                            ctrl_tac_fold_args f env ctrl3
                                              args
                                             in
                                          bind uu____7402
                                            (fun uu____7429  ->
                                               match uu____7429 with
                                               | (args1,ctrl4) ->
                                                   ret
                                                     ((let uu___146_7459 = t3
                                                          in
                                                       {
                                                         FStar_Syntax_Syntax.n
                                                           =
                                                           (FStar_Syntax_Syntax.Tm_app
                                                              (hd2, args1));
                                                         FStar_Syntax_Syntax.pos
                                                           =
                                                           (uu___146_7459.FStar_Syntax_Syntax.pos);
                                                         FStar_Syntax_Syntax.vars
                                                           =
                                                           (uu___146_7459.FStar_Syntax_Syntax.vars)
                                                       }), ctrl4)))
                             | FStar_Syntax_Syntax.Tm_abs (bs,t4,k) ->
                                 let uu____7495 =
                                   FStar_Syntax_Subst.open_term bs t4  in
                                 (match uu____7495 with
                                  | (bs1,t') ->
                                      let uu____7510 =
                                        let uu____7517 =
                                          FStar_TypeChecker_Env.push_binders
                                            env bs1
                                           in
                                        ctrl_tac_fold f uu____7517 ctrl1 t'
                                         in
                                      bind uu____7510
                                        (fun uu____7535  ->
                                           match uu____7535 with
                                           | (t'',ctrl2) ->
                                               let uu____7550 =
                                                 let uu____7557 =
                                                   let uu___147_7560 = t4  in
                                                   let uu____7563 =
                                                     let uu____7564 =
                                                       let uu____7581 =
                                                         FStar_Syntax_Subst.close_binders
                                                           bs1
                                                          in
                                                       let uu____7588 =
                                                         FStar_Syntax_Subst.close
                                                           bs1 t''
                                                          in
                                                       (uu____7581,
                                                         uu____7588, k)
                                                        in
                                                     FStar_Syntax_Syntax.Tm_abs
                                                       uu____7564
                                                      in
                                                   {
                                                     FStar_Syntax_Syntax.n =
                                                       uu____7563;
                                                     FStar_Syntax_Syntax.pos
                                                       =
                                                       (uu___147_7560.FStar_Syntax_Syntax.pos);
                                                     FStar_Syntax_Syntax.vars
                                                       =
                                                       (uu___147_7560.FStar_Syntax_Syntax.vars)
                                                   }  in
                                                 (uu____7557, ctrl2)  in
                                               ret uu____7550))
                             | FStar_Syntax_Syntax.Tm_arrow (bs,k) ->
                                 ret (t3, ctrl1)
                             | uu____7635 -> ret (t3, ctrl1))))

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
              let uu____7678 = ctrl_tac_fold f env ctrl t  in
              bind uu____7678
                (fun uu____7702  ->
                   match uu____7702 with
                   | (t1,ctrl1) ->
                       let uu____7717 = ctrl_tac_fold_args f env ctrl1 ts1
                          in
                       bind uu____7717
                         (fun uu____7744  ->
                            match uu____7744 with
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
              let uu____7826 =
                let uu____7833 =
                  add_irrelevant_goal "dummy" env FStar_Syntax_Util.t_true
                    opts
                   in
                bind uu____7833
                  (fun uu____7842  ->
                     let uu____7843 = ctrl t1  in
                     bind uu____7843
                       (fun res  ->
                          let uu____7866 = trivial ()  in
                          bind uu____7866 (fun uu____7874  -> ret res)))
                 in
              bind uu____7826
                (fun uu____7890  ->
                   match uu____7890 with
                   | (should_rewrite,ctrl1) ->
                       if Prims.op_Negation should_rewrite
                       then ret (t1, ctrl1)
                       else
                         (let uu____7914 =
                            FStar_TypeChecker_TcTerm.tc_term env t1  in
                          match uu____7914 with
                          | (t2,lcomp,g) ->
                              let uu____7930 =
                                (let uu____7933 =
                                   FStar_Syntax_Util.is_pure_or_ghost_lcomp
                                     lcomp
                                    in
                                 Prims.op_Negation uu____7933) ||
                                  (let uu____7935 =
                                     FStar_TypeChecker_Rel.is_trivial g  in
                                   Prims.op_Negation uu____7935)
                                 in
                              if uu____7930
                              then ret (t2, globalStop)
                              else
                                (let typ = lcomp.FStar_Syntax_Syntax.res_typ
                                    in
                                 let uu____7950 =
                                   new_uvar "pointwise_rec" env typ  in
                                 bind uu____7950
                                   (fun ut  ->
                                      log ps
                                        (fun uu____7965  ->
                                           let uu____7966 =
                                             FStar_Syntax_Print.term_to_string
                                               t2
                                              in
                                           let uu____7967 =
                                             FStar_Syntax_Print.term_to_string
                                               ut
                                              in
                                           FStar_Util.print2
                                             "Pointwise_rec: making equality\n\t%s ==\n\t%s\n"
                                             uu____7966 uu____7967);
                                      (let uu____7968 =
                                         let uu____7971 =
                                           let uu____7972 =
                                             FStar_TypeChecker_TcTerm.universe_of
                                               env typ
                                              in
                                           FStar_Syntax_Util.mk_eq2
                                             uu____7972 typ t2 ut
                                            in
                                         add_irrelevant_goal
                                           "rewrite_rec equation" env
                                           uu____7971 opts
                                          in
                                       bind uu____7968
                                         (fun uu____7979  ->
                                            let uu____7980 =
                                              bind rewriter
                                                (fun uu____7994  ->
                                                   let ut1 =
                                                     FStar_TypeChecker_Normalize.reduce_uvar_solutions
                                                       env ut
                                                      in
                                                   log ps
                                                     (fun uu____8000  ->
                                                        let uu____8001 =
                                                          FStar_Syntax_Print.term_to_string
                                                            t2
                                                           in
                                                        let uu____8002 =
                                                          FStar_Syntax_Print.term_to_string
                                                            ut1
                                                           in
                                                        FStar_Util.print2
                                                          "rewrite_rec: succeeded rewriting\n\t%s to\n\t%s\n"
                                                          uu____8001
                                                          uu____8002);
                                                   ret (ut1, ctrl1))
                                               in
                                            focus uu____7980))))))
  
let (topdown_rewrite :
  (FStar_Syntax_Syntax.term ->
     (Prims.bool,FStar_BigInt.t) FStar_Pervasives_Native.tuple2 tac)
    -> unit tac -> unit tac)
  =
  fun ctrl  ->
    fun rewriter  ->
      bind get
        (fun ps  ->
           let uu____8050 =
             match ps.FStar_Tactics_Types.goals with
             | g::gs -> (g, gs)
             | [] -> failwith "Pointwise: no goals"  in
           match uu____8050 with
           | (g,gs) ->
               let gt1 = g.FStar_Tactics_Types.goal_ty  in
               (log ps
                  (fun uu____8087  ->
                     let uu____8088 = FStar_Syntax_Print.term_to_string gt1
                        in
                     FStar_Util.print1 "Topdown_rewrite starting with %s\n"
                       uu____8088);
                bind dismiss_all
                  (fun uu____8091  ->
                     let uu____8092 =
                       ctrl_tac_fold
                         (rewrite_rec ps ctrl rewriter
                            g.FStar_Tactics_Types.opts)
                         g.FStar_Tactics_Types.context keepGoing gt1
                        in
                     bind uu____8092
                       (fun uu____8110  ->
                          match uu____8110 with
                          | (gt',uu____8118) ->
                              (log ps
                                 (fun uu____8122  ->
                                    let uu____8123 =
                                      FStar_Syntax_Print.term_to_string gt'
                                       in
                                    FStar_Util.print1
                                      "Topdown_rewrite seems to have succeded with %s\n"
                                      uu____8123);
                               (let uu____8124 = push_goals gs  in
                                bind uu____8124
                                  (fun uu____8128  ->
                                     add_goals
                                       [(let uu___149_8130 = g  in
                                         {
                                           FStar_Tactics_Types.context =
                                             (uu___149_8130.FStar_Tactics_Types.context);
                                           FStar_Tactics_Types.witness =
                                             (uu___149_8130.FStar_Tactics_Types.witness);
                                           FStar_Tactics_Types.goal_ty = gt';
                                           FStar_Tactics_Types.opts =
                                             (uu___149_8130.FStar_Tactics_Types.opts);
                                           FStar_Tactics_Types.is_guard =
                                             (uu___149_8130.FStar_Tactics_Types.is_guard)
                                         })])))))))
  
let (pointwise : FStar_Tactics_Types.direction -> unit tac -> unit tac) =
  fun d  ->
    fun tau  ->
      bind get
        (fun ps  ->
           let uu____8156 =
             match ps.FStar_Tactics_Types.goals with
             | g::gs -> (g, gs)
             | [] -> failwith "Pointwise: no goals"  in
           match uu____8156 with
           | (g,gs) ->
               let gt1 = g.FStar_Tactics_Types.goal_ty  in
               (log ps
                  (fun uu____8193  ->
                     let uu____8194 = FStar_Syntax_Print.term_to_string gt1
                        in
                     FStar_Util.print1 "Pointwise starting with %s\n"
                       uu____8194);
                bind dismiss_all
                  (fun uu____8197  ->
                     let uu____8198 =
                       tac_fold_env d
                         (pointwise_rec ps tau g.FStar_Tactics_Types.opts)
                         g.FStar_Tactics_Types.context gt1
                        in
                     bind uu____8198
                       (fun gt'  ->
                          log ps
                            (fun uu____8208  ->
                               let uu____8209 =
                                 FStar_Syntax_Print.term_to_string gt'  in
                               FStar_Util.print1
                                 "Pointwise seems to have succeded with %s\n"
                                 uu____8209);
                          (let uu____8210 = push_goals gs  in
                           bind uu____8210
                             (fun uu____8214  ->
                                add_goals
                                  [(let uu___150_8216 = g  in
                                    {
                                      FStar_Tactics_Types.context =
                                        (uu___150_8216.FStar_Tactics_Types.context);
                                      FStar_Tactics_Types.witness =
                                        (uu___150_8216.FStar_Tactics_Types.witness);
                                      FStar_Tactics_Types.goal_ty = gt';
                                      FStar_Tactics_Types.opts =
                                        (uu___150_8216.FStar_Tactics_Types.opts);
                                      FStar_Tactics_Types.is_guard =
                                        (uu___150_8216.FStar_Tactics_Types.is_guard)
                                    })]))))))
  
let (trefl : unit -> unit tac) =
  fun uu____8223  ->
    let uu____8226 = cur_goal ()  in
    bind uu____8226
      (fun g  ->
         let uu____8244 =
           FStar_Syntax_Util.un_squash g.FStar_Tactics_Types.goal_ty  in
         match uu____8244 with
         | FStar_Pervasives_Native.Some t ->
             let uu____8256 = FStar_Syntax_Util.head_and_args' t  in
             (match uu____8256 with
              | (hd1,args) ->
                  let uu____8289 =
                    let uu____8300 =
                      let uu____8301 = FStar_Syntax_Util.un_uinst hd1  in
                      uu____8301.FStar_Syntax_Syntax.n  in
                    (uu____8300, args)  in
                  (match uu____8289 with
                   | (FStar_Syntax_Syntax.Tm_fvar
                      fv,uu____8313::(l,uu____8315)::(r,uu____8317)::[]) when
                       FStar_Syntax_Syntax.fv_eq_lid fv
                         FStar_Parser_Const.eq2_lid
                       ->
                       let uu____8344 =
                         do_unify g.FStar_Tactics_Types.context l r  in
                       bind uu____8344
                         (fun b  ->
                            if Prims.op_Negation b
                            then
                              let uu____8353 =
                                tts g.FStar_Tactics_Types.context l  in
                              let uu____8354 =
                                tts g.FStar_Tactics_Types.context r  in
                              fail2
                                "trefl: not a trivial equality (%s vs %s)"
                                uu____8353 uu____8354
                            else solve g FStar_Syntax_Util.exp_unit)
                   | (hd2,uu____8357) ->
                       let uu____8370 = tts g.FStar_Tactics_Types.context t
                          in
                       fail1 "trefl: not an equality (%s)" uu____8370))
         | FStar_Pervasives_Native.None  -> fail "not an irrelevant goal")
  
let (dup : unit -> unit tac) =
  fun uu____8379  ->
    let uu____8382 = cur_goal ()  in
    bind uu____8382
      (fun g  ->
         let uu____8388 =
           new_uvar "dup" g.FStar_Tactics_Types.context
             g.FStar_Tactics_Types.goal_ty
            in
         bind uu____8388
           (fun u  ->
              let g' =
                let uu___151_8395 = g  in
                {
                  FStar_Tactics_Types.context =
                    (uu___151_8395.FStar_Tactics_Types.context);
                  FStar_Tactics_Types.witness = u;
                  FStar_Tactics_Types.goal_ty =
                    (uu___151_8395.FStar_Tactics_Types.goal_ty);
                  FStar_Tactics_Types.opts =
                    (uu___151_8395.FStar_Tactics_Types.opts);
                  FStar_Tactics_Types.is_guard =
                    (uu___151_8395.FStar_Tactics_Types.is_guard)
                }  in
              bind __dismiss
                (fun uu____8398  ->
                   let uu____8399 =
                     let uu____8402 =
                       let uu____8403 =
                         FStar_TypeChecker_TcTerm.universe_of
                           g.FStar_Tactics_Types.context
                           g.FStar_Tactics_Types.goal_ty
                          in
                       FStar_Syntax_Util.mk_eq2 uu____8403
                         g.FStar_Tactics_Types.goal_ty u
                         g.FStar_Tactics_Types.witness
                        in
                     add_irrelevant_goal "dup equation"
                       g.FStar_Tactics_Types.context uu____8402
                       g.FStar_Tactics_Types.opts
                      in
                   bind uu____8399
                     (fun uu____8406  ->
                        let uu____8407 = add_goals [g']  in
                        bind uu____8407 (fun uu____8411  -> ret ())))))
  
let (flip : unit -> unit tac) =
  fun uu____8418  ->
    bind get
      (fun ps  ->
         match ps.FStar_Tactics_Types.goals with
         | g1::g2::gs ->
             set
               (let uu___152_8435 = ps  in
                {
                  FStar_Tactics_Types.main_context =
                    (uu___152_8435.FStar_Tactics_Types.main_context);
                  FStar_Tactics_Types.main_goal =
                    (uu___152_8435.FStar_Tactics_Types.main_goal);
                  FStar_Tactics_Types.all_implicits =
                    (uu___152_8435.FStar_Tactics_Types.all_implicits);
                  FStar_Tactics_Types.goals = (g2 :: g1 :: gs);
                  FStar_Tactics_Types.smt_goals =
                    (uu___152_8435.FStar_Tactics_Types.smt_goals);
                  FStar_Tactics_Types.depth =
                    (uu___152_8435.FStar_Tactics_Types.depth);
                  FStar_Tactics_Types.__dump =
                    (uu___152_8435.FStar_Tactics_Types.__dump);
                  FStar_Tactics_Types.psc =
                    (uu___152_8435.FStar_Tactics_Types.psc);
                  FStar_Tactics_Types.entry_range =
                    (uu___152_8435.FStar_Tactics_Types.entry_range);
                  FStar_Tactics_Types.guard_policy =
                    (uu___152_8435.FStar_Tactics_Types.guard_policy);
                  FStar_Tactics_Types.freshness =
                    (uu___152_8435.FStar_Tactics_Types.freshness)
                })
         | uu____8436 -> fail "flip: less than 2 goals")
  
let (later : unit -> unit tac) =
  fun uu____8445  ->
    bind get
      (fun ps  ->
         match ps.FStar_Tactics_Types.goals with
         | [] -> ret ()
         | g::gs ->
             set
               (let uu___153_8458 = ps  in
                {
                  FStar_Tactics_Types.main_context =
                    (uu___153_8458.FStar_Tactics_Types.main_context);
                  FStar_Tactics_Types.main_goal =
                    (uu___153_8458.FStar_Tactics_Types.main_goal);
                  FStar_Tactics_Types.all_implicits =
                    (uu___153_8458.FStar_Tactics_Types.all_implicits);
                  FStar_Tactics_Types.goals = (FStar_List.append gs [g]);
                  FStar_Tactics_Types.smt_goals =
                    (uu___153_8458.FStar_Tactics_Types.smt_goals);
                  FStar_Tactics_Types.depth =
                    (uu___153_8458.FStar_Tactics_Types.depth);
                  FStar_Tactics_Types.__dump =
                    (uu___153_8458.FStar_Tactics_Types.__dump);
                  FStar_Tactics_Types.psc =
                    (uu___153_8458.FStar_Tactics_Types.psc);
                  FStar_Tactics_Types.entry_range =
                    (uu___153_8458.FStar_Tactics_Types.entry_range);
                  FStar_Tactics_Types.guard_policy =
                    (uu___153_8458.FStar_Tactics_Types.guard_policy);
                  FStar_Tactics_Types.freshness =
                    (uu___153_8458.FStar_Tactics_Types.freshness)
                }))
  
let (qed : unit -> unit tac) =
  fun uu____8465  ->
    bind get
      (fun ps  ->
         match ps.FStar_Tactics_Types.goals with
         | [] -> ret ()
         | uu____8472 -> fail "Not done!")
  
let (cases :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 tac)
  =
  fun t  ->
    let uu____8492 =
      let uu____8499 = cur_goal ()  in
      bind uu____8499
        (fun g  ->
           let uu____8509 = __tc g.FStar_Tactics_Types.context t  in
           bind uu____8509
             (fun uu____8545  ->
                match uu____8545 with
                | (t1,typ,guard) ->
                    let uu____8561 = FStar_Syntax_Util.head_and_args typ  in
                    (match uu____8561 with
                     | (hd1,args) ->
                         let uu____8604 =
                           let uu____8617 =
                             let uu____8618 = FStar_Syntax_Util.un_uinst hd1
                                in
                             uu____8618.FStar_Syntax_Syntax.n  in
                           (uu____8617, args)  in
                         (match uu____8604 with
                          | (FStar_Syntax_Syntax.Tm_fvar
                             fv,(p,uu____8637)::(q,uu____8639)::[]) when
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
                                let uu___154_8677 = g  in
                                let uu____8678 =
                                  FStar_TypeChecker_Env.push_bv
                                    g.FStar_Tactics_Types.context v_p
                                   in
                                {
                                  FStar_Tactics_Types.context = uu____8678;
                                  FStar_Tactics_Types.witness =
                                    (uu___154_8677.FStar_Tactics_Types.witness);
                                  FStar_Tactics_Types.goal_ty =
                                    (uu___154_8677.FStar_Tactics_Types.goal_ty);
                                  FStar_Tactics_Types.opts =
                                    (uu___154_8677.FStar_Tactics_Types.opts);
                                  FStar_Tactics_Types.is_guard =
                                    (uu___154_8677.FStar_Tactics_Types.is_guard)
                                }  in
                              let g2 =
                                let uu___155_8680 = g  in
                                let uu____8681 =
                                  FStar_TypeChecker_Env.push_bv
                                    g.FStar_Tactics_Types.context v_q
                                   in
                                {
                                  FStar_Tactics_Types.context = uu____8681;
                                  FStar_Tactics_Types.witness =
                                    (uu___155_8680.FStar_Tactics_Types.witness);
                                  FStar_Tactics_Types.goal_ty =
                                    (uu___155_8680.FStar_Tactics_Types.goal_ty);
                                  FStar_Tactics_Types.opts =
                                    (uu___155_8680.FStar_Tactics_Types.opts);
                                  FStar_Tactics_Types.is_guard =
                                    (uu___155_8680.FStar_Tactics_Types.is_guard)
                                }  in
                              bind __dismiss
                                (fun uu____8688  ->
                                   let uu____8689 = add_goals [g1; g2]  in
                                   bind uu____8689
                                     (fun uu____8698  ->
                                        let uu____8699 =
                                          let uu____8704 =
                                            FStar_Syntax_Syntax.bv_to_name
                                              v_p
                                             in
                                          let uu____8705 =
                                            FStar_Syntax_Syntax.bv_to_name
                                              v_q
                                             in
                                          (uu____8704, uu____8705)  in
                                        ret uu____8699))
                          | uu____8710 ->
                              let uu____8723 =
                                tts g.FStar_Tactics_Types.context typ  in
                              fail1 "Not a disjunction: %s" uu____8723))))
       in
    FStar_All.pipe_left (wrap_err "cases") uu____8492
  
let (set_options : Prims.string -> unit tac) =
  fun s  ->
    let uu____8753 = cur_goal ()  in
    bind uu____8753
      (fun g  ->
         FStar_Options.push ();
         (let uu____8766 = FStar_Util.smap_copy g.FStar_Tactics_Types.opts
             in
          FStar_Options.set uu____8766);
         (let res = FStar_Options.set_options FStar_Options.Set s  in
          let opts' = FStar_Options.peek ()  in
          FStar_Options.pop ();
          (match res with
           | FStar_Getopt.Success  ->
               let g' =
                 let uu___156_8773 = g  in
                 {
                   FStar_Tactics_Types.context =
                     (uu___156_8773.FStar_Tactics_Types.context);
                   FStar_Tactics_Types.witness =
                     (uu___156_8773.FStar_Tactics_Types.witness);
                   FStar_Tactics_Types.goal_ty =
                     (uu___156_8773.FStar_Tactics_Types.goal_ty);
                   FStar_Tactics_Types.opts = opts';
                   FStar_Tactics_Types.is_guard =
                     (uu___156_8773.FStar_Tactics_Types.is_guard)
                 }  in
               replace_cur g'
           | FStar_Getopt.Error err ->
               fail2 "Setting options `%s` failed: %s" s err
           | FStar_Getopt.Help  ->
               fail1 "Setting options `%s` failed (got `Help`?)" s)))
  
let (top_env : unit -> env tac) =
  fun uu____8781  ->
    bind get
      (fun ps  -> FStar_All.pipe_left ret ps.FStar_Tactics_Types.main_context)
  
let (cur_env : unit -> env tac) =
  fun uu____8794  ->
    let uu____8797 = cur_goal ()  in
    bind uu____8797
      (fun g  -> FStar_All.pipe_left ret g.FStar_Tactics_Types.context)
  
let (cur_goal' : unit -> FStar_Syntax_Syntax.term tac) =
  fun uu____8810  ->
    let uu____8813 = cur_goal ()  in
    bind uu____8813
      (fun g  -> FStar_All.pipe_left ret g.FStar_Tactics_Types.goal_ty)
  
let (cur_witness : unit -> FStar_Syntax_Syntax.term tac) =
  fun uu____8826  ->
    let uu____8829 = cur_goal ()  in
    bind uu____8829
      (fun g  -> FStar_All.pipe_left ret g.FStar_Tactics_Types.witness)
  
let (unquote :
  FStar_Reflection_Data.typ ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac)
  =
  fun ty  ->
    fun tm  ->
      let uu____8850 =
        let uu____8853 = cur_goal ()  in
        bind uu____8853
          (fun goal  ->
             let env =
               FStar_TypeChecker_Env.set_expected_typ
                 goal.FStar_Tactics_Types.context ty
                in
             let uu____8861 = __tc env tm  in
             bind uu____8861
               (fun uu____8881  ->
                  match uu____8881 with
                  | (tm1,typ,guard) ->
                      let uu____8893 =
                        proc_guard "unquote" env guard
                          goal.FStar_Tactics_Types.opts
                         in
                      bind uu____8893 (fun uu____8897  -> ret tm1)))
         in
      FStar_All.pipe_left (wrap_err "unquote") uu____8850
  
let (uvar_env :
  env ->
    FStar_Reflection_Data.typ FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.term tac)
  =
  fun env  ->
    fun ty  ->
      let uu____8920 =
        match ty with
        | FStar_Pervasives_Native.Some ty1 -> ret ty1
        | FStar_Pervasives_Native.None  ->
            let uu____8926 =
              let uu____8927 = FStar_Syntax_Util.type_u ()  in
              FStar_All.pipe_left FStar_Pervasives_Native.fst uu____8927  in
            new_uvar "uvar_env.2" env uu____8926
         in
      bind uu____8920
        (fun typ  ->
           let uu____8939 = new_uvar "uvar_env" env typ  in
           bind uu____8939 (fun t  -> ret t))
  
let (unshelve : FStar_Syntax_Syntax.term -> unit tac) =
  fun t  ->
    let uu____8953 =
      bind get
        (fun ps  ->
           let env = ps.FStar_Tactics_Types.main_context  in
           let opts =
             match ps.FStar_Tactics_Types.goals with
             | g::uu____8971 -> g.FStar_Tactics_Types.opts
             | uu____8974 -> FStar_Options.peek ()  in
           let uu____8977 = FStar_Syntax_Util.head_and_args t  in
           match uu____8977 with
           | ({
                FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                  (ctx_uvar,uu____8995);
                FStar_Syntax_Syntax.pos = uu____8996;
                FStar_Syntax_Syntax.vars = uu____8997;_},uu____8998)
               ->
               let env1 =
                 let uu___157_9040 = env  in
                 {
                   FStar_TypeChecker_Env.solver =
                     (uu___157_9040.FStar_TypeChecker_Env.solver);
                   FStar_TypeChecker_Env.range =
                     (uu___157_9040.FStar_TypeChecker_Env.range);
                   FStar_TypeChecker_Env.curmodule =
                     (uu___157_9040.FStar_TypeChecker_Env.curmodule);
                   FStar_TypeChecker_Env.gamma =
                     (ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_gamma);
                   FStar_TypeChecker_Env.gamma_sig =
                     (uu___157_9040.FStar_TypeChecker_Env.gamma_sig);
                   FStar_TypeChecker_Env.gamma_cache =
                     (uu___157_9040.FStar_TypeChecker_Env.gamma_cache);
                   FStar_TypeChecker_Env.modules =
                     (uu___157_9040.FStar_TypeChecker_Env.modules);
                   FStar_TypeChecker_Env.expected_typ =
                     (uu___157_9040.FStar_TypeChecker_Env.expected_typ);
                   FStar_TypeChecker_Env.sigtab =
                     (uu___157_9040.FStar_TypeChecker_Env.sigtab);
                   FStar_TypeChecker_Env.is_pattern =
                     (uu___157_9040.FStar_TypeChecker_Env.is_pattern);
                   FStar_TypeChecker_Env.instantiate_imp =
                     (uu___157_9040.FStar_TypeChecker_Env.instantiate_imp);
                   FStar_TypeChecker_Env.effects =
                     (uu___157_9040.FStar_TypeChecker_Env.effects);
                   FStar_TypeChecker_Env.generalize =
                     (uu___157_9040.FStar_TypeChecker_Env.generalize);
                   FStar_TypeChecker_Env.letrecs =
                     (uu___157_9040.FStar_TypeChecker_Env.letrecs);
                   FStar_TypeChecker_Env.top_level =
                     (uu___157_9040.FStar_TypeChecker_Env.top_level);
                   FStar_TypeChecker_Env.check_uvars =
                     (uu___157_9040.FStar_TypeChecker_Env.check_uvars);
                   FStar_TypeChecker_Env.use_eq =
                     (uu___157_9040.FStar_TypeChecker_Env.use_eq);
                   FStar_TypeChecker_Env.is_iface =
                     (uu___157_9040.FStar_TypeChecker_Env.is_iface);
                   FStar_TypeChecker_Env.admit =
                     (uu___157_9040.FStar_TypeChecker_Env.admit);
                   FStar_TypeChecker_Env.lax =
                     (uu___157_9040.FStar_TypeChecker_Env.lax);
                   FStar_TypeChecker_Env.lax_universes =
                     (uu___157_9040.FStar_TypeChecker_Env.lax_universes);
                   FStar_TypeChecker_Env.failhard =
                     (uu___157_9040.FStar_TypeChecker_Env.failhard);
                   FStar_TypeChecker_Env.nosynth =
                     (uu___157_9040.FStar_TypeChecker_Env.nosynth);
                   FStar_TypeChecker_Env.tc_term =
                     (uu___157_9040.FStar_TypeChecker_Env.tc_term);
                   FStar_TypeChecker_Env.type_of =
                     (uu___157_9040.FStar_TypeChecker_Env.type_of);
                   FStar_TypeChecker_Env.universe_of =
                     (uu___157_9040.FStar_TypeChecker_Env.universe_of);
                   FStar_TypeChecker_Env.check_type_of =
                     (uu___157_9040.FStar_TypeChecker_Env.check_type_of);
                   FStar_TypeChecker_Env.use_bv_sorts =
                     (uu___157_9040.FStar_TypeChecker_Env.use_bv_sorts);
                   FStar_TypeChecker_Env.qtbl_name_and_index =
                     (uu___157_9040.FStar_TypeChecker_Env.qtbl_name_and_index);
                   FStar_TypeChecker_Env.normalized_eff_names =
                     (uu___157_9040.FStar_TypeChecker_Env.normalized_eff_names);
                   FStar_TypeChecker_Env.proof_ns =
                     (uu___157_9040.FStar_TypeChecker_Env.proof_ns);
                   FStar_TypeChecker_Env.synth_hook =
                     (uu___157_9040.FStar_TypeChecker_Env.synth_hook);
                   FStar_TypeChecker_Env.splice =
                     (uu___157_9040.FStar_TypeChecker_Env.splice);
                   FStar_TypeChecker_Env.is_native_tactic =
                     (uu___157_9040.FStar_TypeChecker_Env.is_native_tactic);
                   FStar_TypeChecker_Env.identifier_info =
                     (uu___157_9040.FStar_TypeChecker_Env.identifier_info);
                   FStar_TypeChecker_Env.tc_hooks =
                     (uu___157_9040.FStar_TypeChecker_Env.tc_hooks);
                   FStar_TypeChecker_Env.dsenv =
                     (uu___157_9040.FStar_TypeChecker_Env.dsenv);
                   FStar_TypeChecker_Env.dep_graph =
                     (uu___157_9040.FStar_TypeChecker_Env.dep_graph)
                 }  in
               let uu____9041 =
                 let uu____9044 =
                   let uu____9045 = bnorm env1 t  in
                   let uu____9046 =
                     bnorm env1 ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_typ  in
                   {
                     FStar_Tactics_Types.context = env1;
                     FStar_Tactics_Types.witness = uu____9045;
                     FStar_Tactics_Types.goal_ty = uu____9046;
                     FStar_Tactics_Types.opts = opts;
                     FStar_Tactics_Types.is_guard = false
                   }  in
                 [uu____9044]  in
               add_goals uu____9041
           | uu____9047 -> fail "not a uvar")
       in
    FStar_All.pipe_left (wrap_err "unshelve") uu____8953
  
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
          (fun uu____9108  ->
             let uu____9109 = FStar_Options.unsafe_tactic_exec ()  in
             if uu____9109
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
        (fun uu____9130  ->
           let uu____9131 =
             FStar_Syntax_Syntax.gen_bv nm FStar_Pervasives_Native.None t  in
           ret uu____9131)
  
let (change : FStar_Reflection_Data.typ -> unit tac) =
  fun ty  ->
    let uu____9141 =
      mlog
        (fun uu____9146  ->
           let uu____9147 = FStar_Syntax_Print.term_to_string ty  in
           FStar_Util.print1 "change: ty = %s\n" uu____9147)
        (fun uu____9150  ->
           let uu____9151 = cur_goal ()  in
           bind uu____9151
             (fun g  ->
                let uu____9157 = __tc g.FStar_Tactics_Types.context ty  in
                bind uu____9157
                  (fun uu____9177  ->
                     match uu____9177 with
                     | (ty1,uu____9187,guard) ->
                         let uu____9189 =
                           proc_guard "change" g.FStar_Tactics_Types.context
                             guard g.FStar_Tactics_Types.opts
                            in
                         bind uu____9189
                           (fun uu____9194  ->
                              let uu____9195 =
                                do_unify g.FStar_Tactics_Types.context
                                  g.FStar_Tactics_Types.goal_ty ty1
                                 in
                              bind uu____9195
                                (fun bb  ->
                                   if bb
                                   then
                                     replace_cur
                                       (let uu___158_9204 = g  in
                                        {
                                          FStar_Tactics_Types.context =
                                            (uu___158_9204.FStar_Tactics_Types.context);
                                          FStar_Tactics_Types.witness =
                                            (uu___158_9204.FStar_Tactics_Types.witness);
                                          FStar_Tactics_Types.goal_ty = ty1;
                                          FStar_Tactics_Types.opts =
                                            (uu___158_9204.FStar_Tactics_Types.opts);
                                          FStar_Tactics_Types.is_guard =
                                            (uu___158_9204.FStar_Tactics_Types.is_guard)
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
                                      let uu____9211 =
                                        do_unify
                                          g.FStar_Tactics_Types.context ng
                                          nty
                                         in
                                      bind uu____9211
                                        (fun b  ->
                                           if b
                                           then
                                             replace_cur
                                               (let uu___159_9220 = g  in
                                                {
                                                  FStar_Tactics_Types.context
                                                    =
                                                    (uu___159_9220.FStar_Tactics_Types.context);
                                                  FStar_Tactics_Types.witness
                                                    =
                                                    (uu___159_9220.FStar_Tactics_Types.witness);
                                                  FStar_Tactics_Types.goal_ty
                                                    = ty1;
                                                  FStar_Tactics_Types.opts =
                                                    (uu___159_9220.FStar_Tactics_Types.opts);
                                                  FStar_Tactics_Types.is_guard
                                                    =
                                                    (uu___159_9220.FStar_Tactics_Types.is_guard)
                                                })
                                           else fail "not convertible")))))))
       in
    FStar_All.pipe_left (wrap_err "change") uu____9141
  
let rec last : 'a . 'a Prims.list -> 'a =
  fun l  ->
    match l with
    | [] -> failwith "last: empty list"
    | x::[] -> x
    | uu____9242::xs -> last xs
  
let rec init : 'a . 'a Prims.list -> 'a Prims.list =
  fun l  ->
    match l with
    | [] -> failwith "init: empty list"
    | x::[] -> []
    | x::xs -> let uu____9270 = init xs  in x :: uu____9270
  
let rec (inspect :
  FStar_Syntax_Syntax.term -> FStar_Reflection_Data.term_view tac) =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t  in
    let t2 = FStar_Syntax_Util.un_uinst t1  in
    match t2.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_meta (t3,uu____9287) -> inspect t3
    | FStar_Syntax_Syntax.Tm_name bv ->
        FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_Var bv)
    | FStar_Syntax_Syntax.Tm_bvar bv ->
        FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_BVar bv)
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_FVar fv)
    | FStar_Syntax_Syntax.Tm_app (hd1,[]) ->
        failwith "inspect: empty arguments on Tm_app"
    | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
        let uu____9344 = last args  in
        (match uu____9344 with
         | (a,q) ->
             let q' = FStar_Reflection_Basic.inspect_aqual q  in
             let uu____9366 =
               let uu____9367 =
                 let uu____9372 =
                   let uu____9373 =
                     let uu____9378 = init args  in
                     FStar_Syntax_Syntax.mk_Tm_app hd1 uu____9378  in
                   uu____9373 FStar_Pervasives_Native.None
                     t2.FStar_Syntax_Syntax.pos
                    in
                 (uu____9372, (a, q'))  in
               FStar_Reflection_Data.Tv_App uu____9367  in
             FStar_All.pipe_left ret uu____9366)
    | FStar_Syntax_Syntax.Tm_abs ([],uu____9389,uu____9390) ->
        failwith "inspect: empty arguments on Tm_abs"
    | FStar_Syntax_Syntax.Tm_abs (bs,t3,k) ->
        let uu____9434 = FStar_Syntax_Subst.open_term bs t3  in
        (match uu____9434 with
         | (bs1,t4) ->
             (match bs1 with
              | [] -> failwith "impossible"
              | b::bs2 ->
                  let uu____9467 =
                    let uu____9468 =
                      let uu____9473 = FStar_Syntax_Util.abs bs2 t4 k  in
                      (b, uu____9473)  in
                    FStar_Reflection_Data.Tv_Abs uu____9468  in
                  FStar_All.pipe_left ret uu____9467))
    | FStar_Syntax_Syntax.Tm_type uu____9476 ->
        FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_Type ())
    | FStar_Syntax_Syntax.Tm_arrow ([],k) ->
        failwith "inspect: empty binders on arrow"
    | FStar_Syntax_Syntax.Tm_arrow uu____9496 ->
        let uu____9509 = FStar_Syntax_Util.arrow_one t2  in
        (match uu____9509 with
         | FStar_Pervasives_Native.Some (b,c) ->
             FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_Arrow (b, c))
         | FStar_Pervasives_Native.None  -> failwith "impossible")
    | FStar_Syntax_Syntax.Tm_refine (bv,t3) ->
        let b = FStar_Syntax_Syntax.mk_binder bv  in
        let uu____9539 = FStar_Syntax_Subst.open_term [b] t3  in
        (match uu____9539 with
         | (b',t4) ->
             let b1 =
               match b' with
               | b'1::[] -> b'1
               | uu____9578 -> failwith "impossible"  in
             FStar_All.pipe_left ret
               (FStar_Reflection_Data.Tv_Refine
                  ((FStar_Pervasives_Native.fst b1), t4)))
    | FStar_Syntax_Syntax.Tm_constant c ->
        let uu____9586 =
          let uu____9587 = FStar_Reflection_Basic.inspect_const c  in
          FStar_Reflection_Data.Tv_Const uu____9587  in
        FStar_All.pipe_left ret uu____9586
    | FStar_Syntax_Syntax.Tm_uvar (ctx_u,([],uu____9591)) ->
        let uu____9612 =
          let uu____9613 =
            let uu____9622 =
              let uu____9623 =
                FStar_Syntax_Unionfind.uvar_id
                  ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
                 in
              FStar_BigInt.of_int_fs uu____9623  in
            (uu____9622, (ctx_u.FStar_Syntax_Syntax.ctx_uvar_gamma),
              (ctx_u.FStar_Syntax_Syntax.ctx_uvar_binders),
              (ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ))
             in
          FStar_Reflection_Data.Tv_Uvar uu____9613  in
        FStar_All.pipe_left ret uu____9612
    | FStar_Syntax_Syntax.Tm_uvar uu____9626 ->
        failwith "NOT FULLY SUPPORTED"
    | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),t21) ->
        if lb.FStar_Syntax_Syntax.lbunivs <> []
        then FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
        else
          (match lb.FStar_Syntax_Syntax.lbname with
           | FStar_Util.Inr uu____9666 ->
               FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
           | FStar_Util.Inl bv ->
               let b = FStar_Syntax_Syntax.mk_binder bv  in
               let uu____9671 = FStar_Syntax_Subst.open_term [b] t21  in
               (match uu____9671 with
                | (bs,t22) ->
                    let b1 =
                      match bs with
                      | b1::[] -> b1
                      | uu____9710 ->
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
           | FStar_Util.Inr uu____9740 ->
               FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
           | FStar_Util.Inl bv ->
               let uu____9744 = FStar_Syntax_Subst.open_let_rec [lb] t21  in
               (match uu____9744 with
                | (lbs,t22) ->
                    (match lbs with
                     | lb1::[] ->
                         (match lb1.FStar_Syntax_Syntax.lbname with
                          | FStar_Util.Inr uu____9764 ->
                              ret FStar_Reflection_Data.Tv_Unknown
                          | FStar_Util.Inl bv1 ->
                              FStar_All.pipe_left ret
                                (FStar_Reflection_Data.Tv_Let
                                   (true, bv1,
                                     (lb1.FStar_Syntax_Syntax.lbdef), t22)))
                     | uu____9768 ->
                         failwith
                           "impossible: open_term returned different amount of binders")))
    | FStar_Syntax_Syntax.Tm_match (t3,brs) ->
        let rec inspect_pat p =
          match p.FStar_Syntax_Syntax.v with
          | FStar_Syntax_Syntax.Pat_constant c ->
              let uu____9822 = FStar_Reflection_Basic.inspect_const c  in
              FStar_Reflection_Data.Pat_Constant uu____9822
          | FStar_Syntax_Syntax.Pat_cons (fv,ps) ->
              let uu____9841 =
                let uu____9848 =
                  FStar_List.map
                    (fun uu____9860  ->
                       match uu____9860 with
                       | (p1,uu____9868) -> inspect_pat p1) ps
                   in
                (fv, uu____9848)  in
              FStar_Reflection_Data.Pat_Cons uu____9841
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
            (fun uu___91_9952  ->
               match uu___91_9952 with
               | (pat,uu____9970,t4) ->
                   let uu____9984 = inspect_pat pat  in (uu____9984, t4))
            brs1
           in
        FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_Match (t3, brs2))
    | FStar_Syntax_Syntax.Tm_unknown  ->
        FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
    | uu____9991 ->
        ((let uu____9993 =
            let uu____9998 =
              let uu____9999 = FStar_Syntax_Print.tag_of_term t2  in
              let uu____10000 = FStar_Syntax_Print.term_to_string t2  in
              FStar_Util.format2
                "inspect: outside of expected syntax (%s, %s)\n" uu____9999
                uu____10000
               in
            (FStar_Errors.Warning_CantInspect, uu____9998)  in
          FStar_Errors.log_issue t2.FStar_Syntax_Syntax.pos uu____9993);
         FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown)
  
let (pack : FStar_Reflection_Data.term_view -> FStar_Syntax_Syntax.term tac)
  =
  fun tv  ->
    match tv with
    | FStar_Reflection_Data.Tv_Var bv ->
        let uu____10013 = FStar_Syntax_Syntax.bv_to_name bv  in
        FStar_All.pipe_left ret uu____10013
    | FStar_Reflection_Data.Tv_BVar bv ->
        let uu____10017 = FStar_Syntax_Syntax.bv_to_tm bv  in
        FStar_All.pipe_left ret uu____10017
    | FStar_Reflection_Data.Tv_FVar fv ->
        let uu____10021 = FStar_Syntax_Syntax.fv_to_tm fv  in
        FStar_All.pipe_left ret uu____10021
    | FStar_Reflection_Data.Tv_App (l,(r,q)) ->
        let q' = FStar_Reflection_Basic.pack_aqual q  in
        let uu____10028 = FStar_Syntax_Util.mk_app l [(r, q')]  in
        FStar_All.pipe_left ret uu____10028
    | FStar_Reflection_Data.Tv_Abs (b,t) ->
        let uu____10051 =
          FStar_Syntax_Util.abs [b] t FStar_Pervasives_Native.None  in
        FStar_All.pipe_left ret uu____10051
    | FStar_Reflection_Data.Tv_Arrow (b,c) ->
        let uu____10068 = FStar_Syntax_Util.arrow [b] c  in
        FStar_All.pipe_left ret uu____10068
    | FStar_Reflection_Data.Tv_Type () ->
        FStar_All.pipe_left ret FStar_Syntax_Util.ktype
    | FStar_Reflection_Data.Tv_Refine (bv,t) ->
        let uu____10087 = FStar_Syntax_Util.refine bv t  in
        FStar_All.pipe_left ret uu____10087
    | FStar_Reflection_Data.Tv_Const c ->
        let uu____10095 =
          let uu____10098 =
            let uu____10105 =
              let uu____10106 = FStar_Reflection_Basic.pack_const c  in
              FStar_Syntax_Syntax.Tm_constant uu____10106  in
            FStar_Syntax_Syntax.mk uu____10105  in
          uu____10098 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
        FStar_All.pipe_left ret uu____10095
    | FStar_Reflection_Data.Tv_Uvar (u,g,bs,t) ->
        let uu____10118 =
          let uu____10121 = FStar_BigInt.to_int_fs u  in
          FStar_Syntax_Util.uvar_from_id uu____10121 (g, bs, t)  in
        FStar_All.pipe_left ret uu____10118
    | FStar_Reflection_Data.Tv_Let (false ,bv,t1,t2) ->
        let lb =
          FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl bv) []
            bv.FStar_Syntax_Syntax.sort FStar_Parser_Const.effect_Tot_lid t1
            [] FStar_Range.dummyRange
           in
        let uu____10142 =
          let uu____10145 =
            let uu____10152 =
              let uu____10153 =
                let uu____10166 =
                  let uu____10169 =
                    let uu____10170 = FStar_Syntax_Syntax.mk_binder bv  in
                    [uu____10170]  in
                  FStar_Syntax_Subst.close uu____10169 t2  in
                ((false, [lb]), uu____10166)  in
              FStar_Syntax_Syntax.Tm_let uu____10153  in
            FStar_Syntax_Syntax.mk uu____10152  in
          uu____10145 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
        FStar_All.pipe_left ret uu____10142
    | FStar_Reflection_Data.Tv_Let (true ,bv,t1,t2) ->
        let lb =
          FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl bv) []
            bv.FStar_Syntax_Syntax.sort FStar_Parser_Const.effect_Tot_lid t1
            [] FStar_Range.dummyRange
           in
        let uu____10206 = FStar_Syntax_Subst.close_let_rec [lb] t2  in
        (match uu____10206 with
         | (lbs,body) ->
             let uu____10221 =
               FStar_Syntax_Syntax.mk
                 (FStar_Syntax_Syntax.Tm_let ((true, lbs), body))
                 FStar_Pervasives_Native.None FStar_Range.dummyRange
                in
             FStar_All.pipe_left ret uu____10221)
    | FStar_Reflection_Data.Tv_Match (t,brs) ->
        let wrap v1 =
          {
            FStar_Syntax_Syntax.v = v1;
            FStar_Syntax_Syntax.p = FStar_Range.dummyRange
          }  in
        let rec pack_pat p =
          match p with
          | FStar_Reflection_Data.Pat_Constant c ->
              let uu____10259 =
                let uu____10260 = FStar_Reflection_Basic.pack_const c  in
                FStar_Syntax_Syntax.Pat_constant uu____10260  in
              FStar_All.pipe_left wrap uu____10259
          | FStar_Reflection_Data.Pat_Cons (fv,ps) ->
              let uu____10267 =
                let uu____10268 =
                  let uu____10281 =
                    FStar_List.map
                      (fun p1  ->
                         let uu____10297 = pack_pat p1  in
                         (uu____10297, false)) ps
                     in
                  (fv, uu____10281)  in
                FStar_Syntax_Syntax.Pat_cons uu____10268  in
              FStar_All.pipe_left wrap uu____10267
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
            (fun uu___92_10343  ->
               match uu___92_10343 with
               | (pat,t1) ->
                   let uu____10360 = pack_pat pat  in
                   (uu____10360, FStar_Pervasives_Native.None, t1)) brs
           in
        let brs2 = FStar_List.map FStar_Syntax_Subst.close_branch brs1  in
        let uu____10408 =
          FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_match (t, brs2))
            FStar_Pervasives_Native.None FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____10408
    | FStar_Reflection_Data.Tv_AscribedT (e,t,tacopt) ->
        let uu____10440 =
          FStar_Syntax_Syntax.mk
            (FStar_Syntax_Syntax.Tm_ascribed
               (e, ((FStar_Util.Inl t), tacopt),
                 FStar_Pervasives_Native.None)) FStar_Pervasives_Native.None
            FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____10440
    | FStar_Reflection_Data.Tv_AscribedC (e,c,tacopt) ->
        let uu____10490 =
          FStar_Syntax_Syntax.mk
            (FStar_Syntax_Syntax.Tm_ascribed
               (e, ((FStar_Util.Inr c), tacopt),
                 FStar_Pervasives_Native.None)) FStar_Pervasives_Native.None
            FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____10490
    | FStar_Reflection_Data.Tv_Unknown  ->
        let uu____10533 =
          FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
            FStar_Pervasives_Native.None FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____10533
  
let (goal_of_goal_ty :
  env ->
    FStar_Reflection_Data.typ ->
      (FStar_Tactics_Types.goal,FStar_TypeChecker_Env.guard_t)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun typ  ->
      let uu____10554 =
        FStar_TypeChecker_Util.new_implicit_var "proofstate_of_goal_ty"
          typ.FStar_Syntax_Syntax.pos env typ
         in
      match uu____10554 with
      | (u,uu____10572,g_u) ->
          let g =
            let uu____10587 = FStar_Options.peek ()  in
            {
              FStar_Tactics_Types.context = env;
              FStar_Tactics_Types.witness = u;
              FStar_Tactics_Types.goal_ty = typ;
              FStar_Tactics_Types.opts = uu____10587;
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
      let uu____10602 = goal_of_goal_ty env typ  in
      match uu____10602 with
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
  