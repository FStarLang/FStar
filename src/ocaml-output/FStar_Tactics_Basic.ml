open Prims
type goal = FStar_Tactics_Types.goal[@@deriving show]
type name = FStar_Syntax_Syntax.bv[@@deriving show]
type env = FStar_TypeChecker_Env.env[@@deriving show]
type implicits = FStar_TypeChecker_Env.implicits[@@deriving show]
let normalize :
  FStar_TypeChecker_Normalize.step Prims.list ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun s  ->
    fun e  ->
      fun t  ->
        FStar_TypeChecker_Normalize.normalize_with_primitive_steps
          FStar_Reflection_Interpreter.reflection_primops s e t
  
let bnorm :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  = fun e  -> fun t  -> normalize [] e t 
let tts :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> Prims.string =
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
  
let get : FStar_Tactics_Types.proofstate tac =
  mk_tac (fun p  -> FStar_Tactics_Result.Success (p, p)) 
let idtac : unit tac = ret () 
let goal_to_string : FStar_Tactics_Types.goal -> Prims.string =
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
  
let tacprint : Prims.string -> unit =
  fun s  -> FStar_Util.print1 "TAC>> %s\n" s 
let tacprint1 : Prims.string -> Prims.string -> unit =
  fun s  ->
    fun x  ->
      let uu____225 = FStar_Util.format1 s x  in
      FStar_Util.print1 "TAC>> %s\n" uu____225
  
let tacprint2 : Prims.string -> Prims.string -> Prims.string -> unit =
  fun s  ->
    fun x  ->
      fun y  ->
        let uu____241 = FStar_Util.format2 s x y  in
        FStar_Util.print1 "TAC>> %s\n" uu____241
  
let tacprint3 :
  Prims.string -> Prims.string -> Prims.string -> Prims.string -> unit =
  fun s  ->
    fun x  ->
      fun y  ->
        fun z  ->
          let uu____262 = FStar_Util.format3 s x y z  in
          FStar_Util.print1 "TAC>> %s\n" uu____262
  
let comp_to_typ : FStar_Syntax_Syntax.comp -> FStar_Reflection_Data.typ =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total (t,uu____269) -> t
    | FStar_Syntax_Syntax.GTotal (t,uu____279) -> t
    | FStar_Syntax_Syntax.Comp ct -> ct.FStar_Syntax_Syntax.result_typ
  
let is_irrelevant : FStar_Tactics_Types.goal -> Prims.bool =
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
  
let print : Prims.string -> unit tac = fun msg  -> tacprint msg; ret () 
let debug : Prims.string -> unit tac =
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
  
let dump_cur : FStar_Tactics_Types.proofstate -> Prims.string -> unit =
  fun ps  ->
    fun msg  ->
      match ps.FStar_Tactics_Types.goals with
      | [] -> tacprint1 "No more goals (%s)" msg
      | h::uu____366 ->
          (tacprint1 "Current goal (%s):" msg;
           (let uu____370 = FStar_List.hd ps.FStar_Tactics_Types.goals  in
            dump_goal ps uu____370))
  
let ps_to_string :
  (Prims.string,FStar_Tactics_Types.proofstate)
    FStar_Pervasives_Native.tuple2 -> Prims.string
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
  
let goal_to_json : FStar_Tactics_Types.goal -> FStar_Util.json =
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
  
let ps_to_json :
  (Prims.string,FStar_Tactics_Types.proofstate)
    FStar_Pervasives_Native.tuple2 -> FStar_Util.json
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
  
let dump_proofstate : FStar_Tactics_Types.proofstate -> Prims.string -> unit
  =
  fun ps  ->
    fun msg  ->
      FStar_Options.with_saved_options
        (fun uu____635  ->
           FStar_Options.set_option "print_effect_args"
             (FStar_Options.Bool true);
           FStar_Util.print_generic "proof-state" ps_to_string ps_to_json
             (msg, ps))
  
let print_proof_state1 : Prims.string -> unit tac =
  fun msg  ->
    mk_tac
      (fun ps  ->
         let psc = ps.FStar_Tactics_Types.psc  in
         let subst1 = FStar_TypeChecker_Normalize.psc_subst psc  in
         (let uu____658 = FStar_Tactics_Types.subst_proof_state subst1 ps  in
          dump_cur uu____658 msg);
         FStar_Tactics_Result.Success ((), ps))
  
let print_proof_state : Prims.string -> unit tac =
  fun msg  ->
    mk_tac
      (fun ps  ->
         let psc = ps.FStar_Tactics_Types.psc  in
         let subst1 = FStar_TypeChecker_Normalize.psc_subst psc  in
         (let uu____676 = FStar_Tactics_Types.subst_proof_state subst1 ps  in
          dump_proofstate uu____676 msg);
         FStar_Tactics_Result.Success ((), ps))
  
let tac_verb_dbg : Prims.bool FStar_Pervasives_Native.option FStar_ST.ref =
  FStar_Util.mk_ref FStar_Pervasives_Native.None 
let rec log : FStar_Tactics_Types.proofstate -> (unit -> unit) -> unit =
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
                 let uu___65_1004 = ps  in
                 {
                   FStar_Tactics_Types.main_context =
                     (uu___65_1004.FStar_Tactics_Types.main_context);
                   FStar_Tactics_Types.main_goal =
                     (uu___65_1004.FStar_Tactics_Types.main_goal);
                   FStar_Tactics_Types.all_implicits =
                     (uu___65_1004.FStar_Tactics_Types.all_implicits);
                   FStar_Tactics_Types.goals =
                     (uu___65_1004.FStar_Tactics_Types.goals);
                   FStar_Tactics_Types.smt_goals =
                     (uu___65_1004.FStar_Tactics_Types.smt_goals);
                   FStar_Tactics_Types.depth =
                     (uu___65_1004.FStar_Tactics_Types.depth);
                   FStar_Tactics_Types.__dump =
                     (uu___65_1004.FStar_Tactics_Types.__dump);
                   FStar_Tactics_Types.psc =
                     (uu___65_1004.FStar_Tactics_Types.psc);
                   FStar_Tactics_Types.entry_range =
                     (uu___65_1004.FStar_Tactics_Types.entry_range);
                   FStar_Tactics_Types.guard_policy =
                     (uu___65_1004.FStar_Tactics_Types.guard_policy);
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
  
let set : FStar_Tactics_Types.proofstate -> unit tac =
  fun p  -> mk_tac (fun uu____1176  -> FStar_Tactics_Result.Success ((), p)) 
let __do_unify :
  env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool tac
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
  
let do_unify :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool tac
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
  
let trysolve :
  FStar_Tactics_Types.goal -> FStar_Syntax_Syntax.term -> Prims.bool tac =
  fun goal  ->
    fun solution  ->
      do_unify goal.FStar_Tactics_Types.context solution
        goal.FStar_Tactics_Types.witness
  
let __dismiss : unit tac =
  bind get
    (fun p  ->
       let uu____1305 =
         let uu___70_1306 = p  in
         let uu____1307 = FStar_List.tl p.FStar_Tactics_Types.goals  in
         {
           FStar_Tactics_Types.main_context =
             (uu___70_1306.FStar_Tactics_Types.main_context);
           FStar_Tactics_Types.main_goal =
             (uu___70_1306.FStar_Tactics_Types.main_goal);
           FStar_Tactics_Types.all_implicits =
             (uu___70_1306.FStar_Tactics_Types.all_implicits);
           FStar_Tactics_Types.goals = uu____1307;
           FStar_Tactics_Types.smt_goals =
             (uu___70_1306.FStar_Tactics_Types.smt_goals);
           FStar_Tactics_Types.depth =
             (uu___70_1306.FStar_Tactics_Types.depth);
           FStar_Tactics_Types.__dump =
             (uu___70_1306.FStar_Tactics_Types.__dump);
           FStar_Tactics_Types.psc = (uu___70_1306.FStar_Tactics_Types.psc);
           FStar_Tactics_Types.entry_range =
             (uu___70_1306.FStar_Tactics_Types.entry_range);
           FStar_Tactics_Types.guard_policy =
             (uu___70_1306.FStar_Tactics_Types.guard_policy);
           FStar_Tactics_Types.freshness =
             (uu___70_1306.FStar_Tactics_Types.freshness)
         }  in
       set uu____1305)
  
let dismiss : unit -> unit tac =
  fun uu____1316  ->
    bind get
      (fun p  ->
         match p.FStar_Tactics_Types.goals with
         | [] -> fail "dismiss: no more goals"
         | uu____1323 -> __dismiss)
  
let solve : FStar_Tactics_Types.goal -> FStar_Syntax_Syntax.term -> unit tac
  =
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
  
let dismiss_all : unit tac =
  bind get
    (fun p  ->
       set
         (let uu___71_1358 = p  in
          {
            FStar_Tactics_Types.main_context =
              (uu___71_1358.FStar_Tactics_Types.main_context);
            FStar_Tactics_Types.main_goal =
              (uu___71_1358.FStar_Tactics_Types.main_goal);
            FStar_Tactics_Types.all_implicits =
              (uu___71_1358.FStar_Tactics_Types.all_implicits);
            FStar_Tactics_Types.goals = [];
            FStar_Tactics_Types.smt_goals =
              (uu___71_1358.FStar_Tactics_Types.smt_goals);
            FStar_Tactics_Types.depth =
              (uu___71_1358.FStar_Tactics_Types.depth);
            FStar_Tactics_Types.__dump =
              (uu___71_1358.FStar_Tactics_Types.__dump);
            FStar_Tactics_Types.psc = (uu___71_1358.FStar_Tactics_Types.psc);
            FStar_Tactics_Types.entry_range =
              (uu___71_1358.FStar_Tactics_Types.entry_range);
            FStar_Tactics_Types.guard_policy =
              (uu___71_1358.FStar_Tactics_Types.guard_policy);
            FStar_Tactics_Types.freshness =
              (uu___71_1358.FStar_Tactics_Types.freshness)
          }))
  
let nwarn : Prims.int FStar_ST.ref =
  FStar_Util.mk_ref (Prims.lift_native_int (0)) 
let check_valid_goal : FStar_Tactics_Types.goal -> unit =
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
           uu____1416 < (Prims.lift_native_int (5)))
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
             uu____1449 + (Prims.lift_native_int (1))  in
           FStar_ST.op_Colon_Equals nwarn uu____1448))
       else ())
    else ()
  
let add_goals : FStar_Tactics_Types.goal Prims.list -> unit tac =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___72_1517 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___72_1517.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___72_1517.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___72_1517.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (FStar_List.append gs p.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___72_1517.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___72_1517.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___72_1517.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___72_1517.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___72_1517.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___72_1517.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___72_1517.FStar_Tactics_Types.freshness)
            }))
  
let add_smt_goals : FStar_Tactics_Types.goal Prims.list -> unit tac =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___73_1537 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___73_1537.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___73_1537.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___73_1537.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___73_1537.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (FStar_List.append gs p.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___73_1537.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___73_1537.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___73_1537.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___73_1537.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___73_1537.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___73_1537.FStar_Tactics_Types.freshness)
            }))
  
let push_goals : FStar_Tactics_Types.goal Prims.list -> unit tac =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___74_1557 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___74_1557.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___74_1557.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___74_1557.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (FStar_List.append p.FStar_Tactics_Types.goals gs);
              FStar_Tactics_Types.smt_goals =
                (uu___74_1557.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___74_1557.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___74_1557.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___74_1557.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___74_1557.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___74_1557.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___74_1557.FStar_Tactics_Types.freshness)
            }))
  
let push_smt_goals : FStar_Tactics_Types.goal Prims.list -> unit tac =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___75_1577 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___75_1577.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___75_1577.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___75_1577.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___75_1577.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (FStar_List.append p.FStar_Tactics_Types.smt_goals gs);
              FStar_Tactics_Types.depth =
                (uu___75_1577.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___75_1577.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___75_1577.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___75_1577.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___75_1577.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___75_1577.FStar_Tactics_Types.freshness)
            }))
  
let replace_cur : FStar_Tactics_Types.goal -> unit tac =
  fun g  -> bind __dismiss (fun uu____1588  -> add_goals [g]) 
let add_implicits : implicits -> unit tac =
  fun i  ->
    bind get
      (fun p  ->
         set
           (let uu___76_1602 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___76_1602.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___76_1602.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (FStar_List.append i p.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___76_1602.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___76_1602.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___76_1602.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___76_1602.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___76_1602.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___76_1602.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___76_1602.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___76_1602.FStar_Tactics_Types.freshness)
            }))
  
let new_uvar :
  Prims.string ->
    env -> FStar_Reflection_Data.typ -> FStar_Syntax_Syntax.term tac
  =
  fun reason  ->
    fun env  ->
      fun typ  ->
        let uu____1634 =
          FStar_TypeChecker_Util.new_implicit_var reason
            typ.FStar_Syntax_Syntax.pos env typ
           in
        match uu____1634 with
        | (u,uu____1650,g_u) ->
            let uu____1664 =
              add_implicits g_u.FStar_TypeChecker_Env.implicits  in
            bind uu____1664 (fun uu____1668  -> ret u)
  
let is_true : FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____1674 = FStar_Syntax_Util.un_squash t  in
    match uu____1674 with
    | FStar_Pervasives_Native.Some t' ->
        let uu____1684 =
          let uu____1685 = FStar_Syntax_Subst.compress t'  in
          uu____1685.FStar_Syntax_Syntax.n  in
        (match uu____1684 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.true_lid
         | uu____1689 -> false)
    | uu____1690 -> false
  
let is_false : FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____1700 = FStar_Syntax_Util.un_squash t  in
    match uu____1700 with
    | FStar_Pervasives_Native.Some t' ->
        let uu____1710 =
          let uu____1711 = FStar_Syntax_Subst.compress t'  in
          uu____1711.FStar_Syntax_Syntax.n  in
        (match uu____1710 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.false_lid
         | uu____1715 -> false)
    | uu____1716 -> false
  
let cur_goal : unit -> FStar_Tactics_Types.goal tac =
  fun uu____1727  ->
    bind get
      (fun p  ->
         match p.FStar_Tactics_Types.goals with
         | [] -> fail "No more goals (1)"
         | hd1::tl1 -> ret hd1)
  
let tadmit : unit -> unit tac =
  fun uu____1744  ->
    let uu____1747 =
      let uu____1750 = cur_goal ()  in
      bind uu____1750
        (fun g  ->
           (let uu____1757 =
              let uu____1762 =
                let uu____1763 = goal_to_string g  in
                FStar_Util.format1 "Tactics admitted goal <%s>\n\n"
                  uu____1763
                 in
              (FStar_Errors.Warning_TacAdmit, uu____1762)  in
            FStar_Errors.log_issue
              (g.FStar_Tactics_Types.goal_ty).FStar_Syntax_Syntax.pos
              uu____1757);
           solve g FStar_Syntax_Util.exp_unit)
       in
    FStar_All.pipe_left (wrap_err "tadmit") uu____1747
  
let fresh : unit -> FStar_BigInt.t tac =
  fun uu____1774  ->
    bind get
      (fun ps  ->
         let n1 = ps.FStar_Tactics_Types.freshness  in
         let ps1 =
           let uu___77_1784 = ps  in
           {
             FStar_Tactics_Types.main_context =
               (uu___77_1784.FStar_Tactics_Types.main_context);
             FStar_Tactics_Types.main_goal =
               (uu___77_1784.FStar_Tactics_Types.main_goal);
             FStar_Tactics_Types.all_implicits =
               (uu___77_1784.FStar_Tactics_Types.all_implicits);
             FStar_Tactics_Types.goals =
               (uu___77_1784.FStar_Tactics_Types.goals);
             FStar_Tactics_Types.smt_goals =
               (uu___77_1784.FStar_Tactics_Types.smt_goals);
             FStar_Tactics_Types.depth =
               (uu___77_1784.FStar_Tactics_Types.depth);
             FStar_Tactics_Types.__dump =
               (uu___77_1784.FStar_Tactics_Types.__dump);
             FStar_Tactics_Types.psc = (uu___77_1784.FStar_Tactics_Types.psc);
             FStar_Tactics_Types.entry_range =
               (uu___77_1784.FStar_Tactics_Types.entry_range);
             FStar_Tactics_Types.guard_policy =
               (uu___77_1784.FStar_Tactics_Types.guard_policy);
             FStar_Tactics_Types.freshness =
               (n1 + (Prims.lift_native_int (1)))
           }  in
         let uu____1785 = set ps1  in
         bind uu____1785
           (fun uu____1790  ->
              let uu____1791 = FStar_BigInt.of_int_fs n1  in ret uu____1791))
  
let ngoals : unit -> FStar_BigInt.t tac =
  fun uu____1798  ->
    bind get
      (fun ps  ->
         let n1 = FStar_List.length ps.FStar_Tactics_Types.goals  in
         let uu____1806 = FStar_BigInt.of_int_fs n1  in ret uu____1806)
  
let ngoals_smt : unit -> FStar_BigInt.t tac =
  fun uu____1819  ->
    bind get
      (fun ps  ->
         let n1 = FStar_List.length ps.FStar_Tactics_Types.smt_goals  in
         let uu____1827 = FStar_BigInt.of_int_fs n1  in ret uu____1827)
  
let is_guard : unit -> Prims.bool tac =
  fun uu____1840  ->
    let uu____1843 = cur_goal ()  in
    bind uu____1843 (fun g  -> ret g.FStar_Tactics_Types.is_guard)
  
let mk_irrelevant_goal :
  Prims.string ->
    env ->
      FStar_Reflection_Data.typ ->
        FStar_Options.optionstate -> FStar_Tactics_Types.goal tac
  =
  fun reason  ->
    fun env  ->
      fun phi  ->
        fun opts  ->
          let typ =
            let uu____1875 = env.FStar_TypeChecker_Env.universe_of env phi
               in
            FStar_Syntax_Util.mk_squash uu____1875 phi  in
          let uu____1876 = new_uvar reason env typ  in
          bind uu____1876
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
  
let __tc :
  env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term,FStar_Reflection_Data.typ,FStar_TypeChecker_Env.guard_t)
        FStar_Pervasives_Native.tuple3 tac
  =
  fun e  ->
    fun t  ->
      bind get
        (fun ps  ->
           mlog
             (fun uu____1925  ->
                let uu____1926 = tts e t  in
                FStar_Util.print1 "Tac> __tc(%s)\n" uu____1926)
             (fun uu____1928  ->
                try
                  let uu____1948 =
                    (ps.FStar_Tactics_Types.main_context).FStar_TypeChecker_Env.type_of
                      e t
                     in
                  ret uu____1948
                with
                | FStar_Errors.Err (uu____1975,msg) ->
                    let uu____1977 = tts e t  in
                    let uu____1978 =
                      let uu____1979 = FStar_TypeChecker_Env.all_binders e
                         in
                      FStar_All.pipe_right uu____1979
                        (FStar_Syntax_Print.binders_to_string ", ")
                       in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____1977 uu____1978 msg
                | FStar_Errors.Error (uu____1986,msg,uu____1988) ->
                    let uu____1989 = tts e t  in
                    let uu____1990 =
                      let uu____1991 = FStar_TypeChecker_Env.all_binders e
                         in
                      FStar_All.pipe_right uu____1991
                        (FStar_Syntax_Print.binders_to_string ", ")
                       in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____1989 uu____1990 msg))
  
let istrivial : env -> FStar_Syntax_Syntax.term -> Prims.bool =
  fun e  ->
    fun t  ->
      let steps =
        [FStar_TypeChecker_Normalize.Reify;
        FStar_TypeChecker_Normalize.UnfoldUntil
          FStar_Syntax_Syntax.Delta_constant;
        FStar_TypeChecker_Normalize.Primops;
        FStar_TypeChecker_Normalize.Simplify;
        FStar_TypeChecker_Normalize.UnfoldTac;
        FStar_TypeChecker_Normalize.Unmeta]  in
      let t1 = normalize steps e t  in is_true t1
  
let get_guard_policy : unit -> FStar_Tactics_Types.guard_policy tac =
  fun uu____2018  ->
    bind get (fun ps  -> ret ps.FStar_Tactics_Types.guard_policy)
  
let set_guard_policy : FStar_Tactics_Types.guard_policy -> unit tac =
  fun pol  ->
    bind get
      (fun ps  ->
         set
           (let uu___80_2036 = ps  in
            {
              FStar_Tactics_Types.main_context =
                (uu___80_2036.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___80_2036.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___80_2036.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___80_2036.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___80_2036.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___80_2036.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___80_2036.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___80_2036.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___80_2036.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy = pol;
              FStar_Tactics_Types.freshness =
                (uu___80_2036.FStar_Tactics_Types.freshness)
            }))
  
let with_policy : 'a . FStar_Tactics_Types.guard_policy -> 'a tac -> 'a tac =
  fun pol  ->
    fun t  ->
      let uu____2060 = get_guard_policy ()  in
      bind uu____2060
        (fun old_pol  ->
           let uu____2066 = set_guard_policy pol  in
           bind uu____2066
             (fun uu____2070  ->
                bind t
                  (fun r  ->
                     let uu____2074 = set_guard_policy old_pol  in
                     bind uu____2074 (fun uu____2078  -> ret r))))
  
let proc_guard :
  Prims.string ->
    env ->
      FStar_TypeChecker_Env.guard_t -> FStar_Options.optionstate -> unit tac
  =
  fun reason  ->
    fun e  ->
      fun g  ->
        fun opts  ->
          let uu____2103 =
            let uu____2104 = FStar_TypeChecker_Rel.simplify_guard e g  in
            uu____2104.FStar_TypeChecker_Env.guard_f  in
          match uu____2103 with
          | FStar_TypeChecker_Common.Trivial  -> ret ()
          | FStar_TypeChecker_Common.NonTrivial f ->
              let uu____2108 = istrivial e f  in
              if uu____2108
              then ret ()
              else
                bind get
                  (fun ps  ->
                     match ps.FStar_Tactics_Types.guard_policy with
                     | FStar_Tactics_Types.Drop  -> ret ()
                     | FStar_Tactics_Types.Goal  ->
                         let uu____2116 = mk_irrelevant_goal reason e f opts
                            in
                         bind uu____2116
                           (fun goal  ->
                              let goal1 =
                                let uu___81_2123 = goal  in
                                {
                                  FStar_Tactics_Types.context =
                                    (uu___81_2123.FStar_Tactics_Types.context);
                                  FStar_Tactics_Types.witness =
                                    (uu___81_2123.FStar_Tactics_Types.witness);
                                  FStar_Tactics_Types.goal_ty =
                                    (uu___81_2123.FStar_Tactics_Types.goal_ty);
                                  FStar_Tactics_Types.opts =
                                    (uu___81_2123.FStar_Tactics_Types.opts);
                                  FStar_Tactics_Types.is_guard = true
                                }  in
                              push_goals [goal1])
                     | FStar_Tactics_Types.SMT  ->
                         let uu____2124 = mk_irrelevant_goal reason e f opts
                            in
                         bind uu____2124
                           (fun goal  ->
                              let goal1 =
                                let uu___82_2131 = goal  in
                                {
                                  FStar_Tactics_Types.context =
                                    (uu___82_2131.FStar_Tactics_Types.context);
                                  FStar_Tactics_Types.witness =
                                    (uu___82_2131.FStar_Tactics_Types.witness);
                                  FStar_Tactics_Types.goal_ty =
                                    (uu___82_2131.FStar_Tactics_Types.goal_ty);
                                  FStar_Tactics_Types.opts =
                                    (uu___82_2131.FStar_Tactics_Types.opts);
                                  FStar_Tactics_Types.is_guard = true
                                }  in
                              push_smt_goals [goal1])
                     | FStar_Tactics_Types.Force  ->
                         (try
                            let uu____2139 =
                              let uu____2140 =
                                let uu____2141 =
                                  FStar_TypeChecker_Rel.discharge_guard_no_smt
                                    e g
                                   in
                                FStar_All.pipe_left
                                  FStar_TypeChecker_Rel.is_trivial uu____2141
                                 in
                              Prims.op_Negation uu____2140  in
                            if uu____2139
                            then
                              mlog
                                (fun uu____2146  ->
                                   let uu____2147 =
                                     FStar_TypeChecker_Rel.guard_to_string e
                                       g
                                      in
                                   FStar_Util.print1 "guard = %s\n"
                                     uu____2147)
                                (fun uu____2149  ->
                                   fail1 "Forcing the guard failed %s)"
                                     reason)
                            else ret ()
                          with
                          | uu____2156 ->
                              mlog
                                (fun uu____2159  ->
                                   let uu____2160 =
                                     FStar_TypeChecker_Rel.guard_to_string e
                                       g
                                      in
                                   FStar_Util.print1 "guard = %s\n"
                                     uu____2160)
                                (fun uu____2162  ->
                                   fail1 "Forcing the guard failed (%s)"
                                     reason)))
  
let tc : FStar_Syntax_Syntax.term -> FStar_Reflection_Data.typ tac =
  fun t  ->
    let uu____2172 =
      let uu____2175 = cur_goal ()  in
      bind uu____2175
        (fun goal  ->
           let uu____2181 = __tc goal.FStar_Tactics_Types.context t  in
           bind uu____2181
             (fun uu____2201  ->
                match uu____2201 with
                | (t1,typ,guard) ->
                    let uu____2213 =
                      proc_guard "tc" goal.FStar_Tactics_Types.context guard
                        goal.FStar_Tactics_Types.opts
                       in
                    bind uu____2213 (fun uu____2217  -> ret typ)))
       in
    FStar_All.pipe_left (wrap_err "tc") uu____2172
  
let add_irrelevant_goal :
  Prims.string ->
    env -> FStar_Reflection_Data.typ -> FStar_Options.optionstate -> unit tac
  =
  fun reason  ->
    fun env  ->
      fun phi  ->
        fun opts  ->
          let uu____2246 = mk_irrelevant_goal reason env phi opts  in
          bind uu____2246 (fun goal  -> add_goals [goal])
  
let trivial : unit -> unit tac =
  fun uu____2257  ->
    let uu____2260 = cur_goal ()  in
    bind uu____2260
      (fun goal  ->
         let uu____2266 =
           istrivial goal.FStar_Tactics_Types.context
             goal.FStar_Tactics_Types.goal_ty
            in
         if uu____2266
         then solve goal FStar_Syntax_Util.exp_unit
         else
           (let uu____2270 =
              tts goal.FStar_Tactics_Types.context
                goal.FStar_Tactics_Types.goal_ty
               in
            fail1 "Not a trivial goal: %s" uu____2270))
  
let goal_from_guard :
  Prims.string ->
    env ->
      FStar_TypeChecker_Env.guard_t ->
        FStar_Options.optionstate ->
          FStar_Tactics_Types.goal FStar_Pervasives_Native.option tac
  =
  fun reason  ->
    fun e  ->
      fun g  ->
        fun opts  ->
          let uu____2299 =
            let uu____2300 = FStar_TypeChecker_Rel.simplify_guard e g  in
            uu____2300.FStar_TypeChecker_Env.guard_f  in
          match uu____2299 with
          | FStar_TypeChecker_Common.Trivial  ->
              ret FStar_Pervasives_Native.None
          | FStar_TypeChecker_Common.NonTrivial f ->
              let uu____2308 = istrivial e f  in
              if uu____2308
              then ret FStar_Pervasives_Native.None
              else
                (let uu____2316 = mk_irrelevant_goal reason e f opts  in
                 bind uu____2316
                   (fun goal  ->
                      ret
                        (FStar_Pervasives_Native.Some
                           (let uu___85_2326 = goal  in
                            {
                              FStar_Tactics_Types.context =
                                (uu___85_2326.FStar_Tactics_Types.context);
                              FStar_Tactics_Types.witness =
                                (uu___85_2326.FStar_Tactics_Types.witness);
                              FStar_Tactics_Types.goal_ty =
                                (uu___85_2326.FStar_Tactics_Types.goal_ty);
                              FStar_Tactics_Types.opts =
                                (uu___85_2326.FStar_Tactics_Types.opts);
                              FStar_Tactics_Types.is_guard = true
                            }))))
  
let smt : unit -> unit tac =
  fun uu____2333  ->
    let uu____2336 = cur_goal ()  in
    bind uu____2336
      (fun g  ->
         let uu____2342 = is_irrelevant g  in
         if uu____2342
         then bind __dismiss (fun uu____2346  -> add_smt_goals [g])
         else
           (let uu____2348 =
              tts g.FStar_Tactics_Types.context g.FStar_Tactics_Types.goal_ty
               in
            fail1 "goal is not irrelevant: cannot dispatch to smt (%s)"
              uu____2348))
  
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
             let uu____2397 =
               try
                 let uu____2431 =
                   let uu____2440 = FStar_BigInt.to_int_fs n1  in
                   FStar_List.splitAt uu____2440 p.FStar_Tactics_Types.goals
                    in
                 ret uu____2431
               with | uu____2462 -> fail "divide: not enough goals"  in
             bind uu____2397
               (fun uu____2489  ->
                  match uu____2489 with
                  | (lgs,rgs) ->
                      let lp =
                        let uu___86_2515 = p  in
                        {
                          FStar_Tactics_Types.main_context =
                            (uu___86_2515.FStar_Tactics_Types.main_context);
                          FStar_Tactics_Types.main_goal =
                            (uu___86_2515.FStar_Tactics_Types.main_goal);
                          FStar_Tactics_Types.all_implicits =
                            (uu___86_2515.FStar_Tactics_Types.all_implicits);
                          FStar_Tactics_Types.goals = lgs;
                          FStar_Tactics_Types.smt_goals = [];
                          FStar_Tactics_Types.depth =
                            (uu___86_2515.FStar_Tactics_Types.depth);
                          FStar_Tactics_Types.__dump =
                            (uu___86_2515.FStar_Tactics_Types.__dump);
                          FStar_Tactics_Types.psc =
                            (uu___86_2515.FStar_Tactics_Types.psc);
                          FStar_Tactics_Types.entry_range =
                            (uu___86_2515.FStar_Tactics_Types.entry_range);
                          FStar_Tactics_Types.guard_policy =
                            (uu___86_2515.FStar_Tactics_Types.guard_policy);
                          FStar_Tactics_Types.freshness =
                            (uu___86_2515.FStar_Tactics_Types.freshness)
                        }  in
                      let rp =
                        let uu___87_2517 = p  in
                        {
                          FStar_Tactics_Types.main_context =
                            (uu___87_2517.FStar_Tactics_Types.main_context);
                          FStar_Tactics_Types.main_goal =
                            (uu___87_2517.FStar_Tactics_Types.main_goal);
                          FStar_Tactics_Types.all_implicits =
                            (uu___87_2517.FStar_Tactics_Types.all_implicits);
                          FStar_Tactics_Types.goals = rgs;
                          FStar_Tactics_Types.smt_goals = [];
                          FStar_Tactics_Types.depth =
                            (uu___87_2517.FStar_Tactics_Types.depth);
                          FStar_Tactics_Types.__dump =
                            (uu___87_2517.FStar_Tactics_Types.__dump);
                          FStar_Tactics_Types.psc =
                            (uu___87_2517.FStar_Tactics_Types.psc);
                          FStar_Tactics_Types.entry_range =
                            (uu___87_2517.FStar_Tactics_Types.entry_range);
                          FStar_Tactics_Types.guard_policy =
                            (uu___87_2517.FStar_Tactics_Types.guard_policy);
                          FStar_Tactics_Types.freshness =
                            (uu___87_2517.FStar_Tactics_Types.freshness)
                        }  in
                      let uu____2518 = set lp  in
                      bind uu____2518
                        (fun uu____2526  ->
                           bind l
                             (fun a  ->
                                bind get
                                  (fun lp'  ->
                                     let uu____2540 = set rp  in
                                     bind uu____2540
                                       (fun uu____2548  ->
                                          bind r
                                            (fun b  ->
                                               bind get
                                                 (fun rp'  ->
                                                    let p' =
                                                      let uu___88_2564 = p
                                                         in
                                                      {
                                                        FStar_Tactics_Types.main_context
                                                          =
                                                          (uu___88_2564.FStar_Tactics_Types.main_context);
                                                        FStar_Tactics_Types.main_goal
                                                          =
                                                          (uu___88_2564.FStar_Tactics_Types.main_goal);
                                                        FStar_Tactics_Types.all_implicits
                                                          =
                                                          (uu___88_2564.FStar_Tactics_Types.all_implicits);
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
                                                          (uu___88_2564.FStar_Tactics_Types.depth);
                                                        FStar_Tactics_Types.__dump
                                                          =
                                                          (uu___88_2564.FStar_Tactics_Types.__dump);
                                                        FStar_Tactics_Types.psc
                                                          =
                                                          (uu___88_2564.FStar_Tactics_Types.psc);
                                                        FStar_Tactics_Types.entry_range
                                                          =
                                                          (uu___88_2564.FStar_Tactics_Types.entry_range);
                                                        FStar_Tactics_Types.guard_policy
                                                          =
                                                          (uu___88_2564.FStar_Tactics_Types.guard_policy);
                                                        FStar_Tactics_Types.freshness
                                                          =
                                                          (uu___88_2564.FStar_Tactics_Types.freshness)
                                                      }  in
                                                    let uu____2565 = set p'
                                                       in
                                                    bind uu____2565
                                                      (fun uu____2573  ->
                                                         ret (a, b))))))))))
  
let focus : 'a . 'a tac -> 'a tac =
  fun f  ->
    let uu____2594 = divide FStar_BigInt.one f idtac  in
    bind uu____2594
      (fun uu____2607  -> match uu____2607 with | (a,()) -> ret a)
  
let rec map : 'a . 'a tac -> 'a Prims.list tac =
  fun tau  ->
    bind get
      (fun p  ->
         match p.FStar_Tactics_Types.goals with
         | [] -> ret []
         | uu____2644::uu____2645 ->
             let uu____2648 =
               let uu____2657 = map tau  in
               divide FStar_BigInt.one tau uu____2657  in
             bind uu____2648
               (fun uu____2675  ->
                  match uu____2675 with | (h,t) -> ret (h :: t)))
  
let seq : unit tac -> unit tac -> unit tac =
  fun t1  ->
    fun t2  ->
      let uu____2716 =
        bind t1
          (fun uu____2721  ->
             let uu____2722 = map t2  in
             bind uu____2722 (fun uu____2730  -> ret ()))
         in
      focus uu____2716
  
let intro : unit -> FStar_Syntax_Syntax.binder tac =
  fun uu____2739  ->
    let uu____2742 =
      let uu____2745 = cur_goal ()  in
      bind uu____2745
        (fun goal  ->
           let uu____2754 =
             FStar_Syntax_Util.arrow_one goal.FStar_Tactics_Types.goal_ty  in
           match uu____2754 with
           | FStar_Pervasives_Native.Some (b,c) ->
               let uu____2769 =
                 let uu____2770 = FStar_Syntax_Util.is_total_comp c  in
                 Prims.op_Negation uu____2770  in
               if uu____2769
               then fail "Codomain is effectful"
               else
                 (let env' =
                    FStar_TypeChecker_Env.push_binders
                      goal.FStar_Tactics_Types.context [b]
                     in
                  let typ' = comp_to_typ c  in
                  let uu____2776 = new_uvar "intro" env' typ'  in
                  bind uu____2776
                    (fun u  ->
                       let uu____2782 =
                         let uu____2785 =
                           FStar_Syntax_Util.abs [b] u
                             FStar_Pervasives_Native.None
                            in
                         trysolve goal uu____2785  in
                       bind uu____2782
                         (fun bb  ->
                            if bb
                            then
                              let uu____2791 =
                                let uu____2794 =
                                  let uu___91_2795 = goal  in
                                  let uu____2796 = bnorm env' u  in
                                  let uu____2797 = bnorm env' typ'  in
                                  {
                                    FStar_Tactics_Types.context = env';
                                    FStar_Tactics_Types.witness = uu____2796;
                                    FStar_Tactics_Types.goal_ty = uu____2797;
                                    FStar_Tactics_Types.opts =
                                      (uu___91_2795.FStar_Tactics_Types.opts);
                                    FStar_Tactics_Types.is_guard =
                                      (uu___91_2795.FStar_Tactics_Types.is_guard)
                                  }  in
                                replace_cur uu____2794  in
                              bind uu____2791 (fun uu____2799  -> ret b)
                            else fail "unification failed")))
           | FStar_Pervasives_Native.None  ->
               let uu____2805 =
                 tts goal.FStar_Tactics_Types.context
                   goal.FStar_Tactics_Types.goal_ty
                  in
               fail1 "goal is not an arrow (%s)" uu____2805)
       in
    FStar_All.pipe_left (wrap_err "intro") uu____2742
  
let intro_rec :
  unit ->
    (FStar_Syntax_Syntax.binder,FStar_Syntax_Syntax.binder)
      FStar_Pervasives_Native.tuple2 tac
  =
  fun uu____2820  ->
    let uu____2827 = cur_goal ()  in
    bind uu____2827
      (fun goal  ->
         FStar_Util.print_string
           "WARNING (intro_rec): calling this is known to cause normalizer loops\n";
         FStar_Util.print_string
           "WARNING (intro_rec): proceed at your own risk...\n";
         (let uu____2844 =
            FStar_Syntax_Util.arrow_one goal.FStar_Tactics_Types.goal_ty  in
          match uu____2844 with
          | FStar_Pervasives_Native.Some (b,c) ->
              let uu____2863 =
                let uu____2864 = FStar_Syntax_Util.is_total_comp c  in
                Prims.op_Negation uu____2864  in
              if uu____2863
              then fail "Codomain is effectful"
              else
                (let bv =
                   FStar_Syntax_Syntax.gen_bv "__recf"
                     FStar_Pervasives_Native.None
                     goal.FStar_Tactics_Types.goal_ty
                    in
                 let bs =
                   let uu____2880 = FStar_Syntax_Syntax.mk_binder bv  in
                   [uu____2880; b]  in
                 let env' =
                   FStar_TypeChecker_Env.push_binders
                     goal.FStar_Tactics_Types.context bs
                    in
                 let uu____2882 =
                   let uu____2885 = comp_to_typ c  in
                   new_uvar "intro_rec" env' uu____2885  in
                 bind uu____2882
                   (fun u  ->
                      let lb =
                        let uu____2900 =
                          FStar_Syntax_Util.abs [b] u
                            FStar_Pervasives_Native.None
                           in
                        FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl bv)
                          [] goal.FStar_Tactics_Types.goal_ty
                          FStar_Parser_Const.effect_Tot_lid uu____2900 []
                          FStar_Range.dummyRange
                         in
                      let body = FStar_Syntax_Syntax.bv_to_name bv  in
                      let uu____2906 =
                        FStar_Syntax_Subst.close_let_rec [lb] body  in
                      match uu____2906 with
                      | (lbs,body1) ->
                          let tm =
                            FStar_Syntax_Syntax.mk
                              (FStar_Syntax_Syntax.Tm_let
                                 ((true, lbs), body1))
                              FStar_Pervasives_Native.None
                              (goal.FStar_Tactics_Types.witness).FStar_Syntax_Syntax.pos
                             in
                          let uu____2936 = trysolve goal tm  in
                          bind uu____2936
                            (fun bb  ->
                               if bb
                               then
                                 let uu____2952 =
                                   let uu____2955 =
                                     let uu___92_2956 = goal  in
                                     let uu____2957 = bnorm env' u  in
                                     let uu____2958 =
                                       let uu____2959 = comp_to_typ c  in
                                       bnorm env' uu____2959  in
                                     {
                                       FStar_Tactics_Types.context = env';
                                       FStar_Tactics_Types.witness =
                                         uu____2957;
                                       FStar_Tactics_Types.goal_ty =
                                         uu____2958;
                                       FStar_Tactics_Types.opts =
                                         (uu___92_2956.FStar_Tactics_Types.opts);
                                       FStar_Tactics_Types.is_guard =
                                         (uu___92_2956.FStar_Tactics_Types.is_guard)
                                     }  in
                                   replace_cur uu____2955  in
                                 bind uu____2952
                                   (fun uu____2966  ->
                                      let uu____2967 =
                                        let uu____2972 =
                                          FStar_Syntax_Syntax.mk_binder bv
                                           in
                                        (uu____2972, b)  in
                                      ret uu____2967)
                               else fail "intro_rec: unification failed")))
          | FStar_Pervasives_Native.None  ->
              let uu____2986 =
                tts goal.FStar_Tactics_Types.context
                  goal.FStar_Tactics_Types.goal_ty
                 in
              fail1 "intro_rec: goal is not an arrow (%s)" uu____2986))
  
let norm : FStar_Syntax_Embeddings.norm_step Prims.list -> unit tac =
  fun s  ->
    let uu____3004 = cur_goal ()  in
    bind uu____3004
      (fun goal  ->
         mlog
           (fun uu____3011  ->
              let uu____3012 =
                FStar_Syntax_Print.term_to_string
                  goal.FStar_Tactics_Types.witness
                 in
              FStar_Util.print1 "norm: witness = %s\n" uu____3012)
           (fun uu____3017  ->
              let steps =
                let uu____3021 = FStar_TypeChecker_Normalize.tr_norm_steps s
                   in
                FStar_List.append
                  [FStar_TypeChecker_Normalize.Reify;
                  FStar_TypeChecker_Normalize.UnfoldTac] uu____3021
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
                (let uu___93_3028 = goal  in
                 {
                   FStar_Tactics_Types.context =
                     (uu___93_3028.FStar_Tactics_Types.context);
                   FStar_Tactics_Types.witness = w;
                   FStar_Tactics_Types.goal_ty = t;
                   FStar_Tactics_Types.opts =
                     (uu___93_3028.FStar_Tactics_Types.opts);
                   FStar_Tactics_Types.is_guard =
                     (uu___93_3028.FStar_Tactics_Types.is_guard)
                 })))
  
let norm_term_env :
  env ->
    FStar_Syntax_Embeddings.norm_step Prims.list ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac
  =
  fun e  ->
    fun s  ->
      fun t  ->
        let uu____3052 =
          mlog
            (fun uu____3057  ->
               let uu____3058 = FStar_Syntax_Print.term_to_string t  in
               FStar_Util.print1 "norm_term: tm = %s\n" uu____3058)
            (fun uu____3060  ->
               bind get
                 (fun ps  ->
                    let opts =
                      match ps.FStar_Tactics_Types.goals with
                      | g::uu____3066 -> g.FStar_Tactics_Types.opts
                      | uu____3069 -> FStar_Options.peek ()  in
                    mlog
                      (fun uu____3074  ->
                         let uu____3075 =
                           tts ps.FStar_Tactics_Types.main_context t  in
                         FStar_Util.print1 "norm_term_env: t = %s\n"
                           uu____3075)
                      (fun uu____3078  ->
                         let uu____3079 = __tc e t  in
                         bind uu____3079
                           (fun uu____3100  ->
                              match uu____3100 with
                              | (t1,uu____3110,uu____3111) ->
                                  let steps =
                                    let uu____3115 =
                                      FStar_TypeChecker_Normalize.tr_norm_steps
                                        s
                                       in
                                    FStar_List.append
                                      [FStar_TypeChecker_Normalize.Reify;
                                      FStar_TypeChecker_Normalize.UnfoldTac]
                                      uu____3115
                                     in
                                  let t2 =
                                    normalize steps
                                      ps.FStar_Tactics_Types.main_context t1
                                     in
                                  ret t2))))
           in
        FStar_All.pipe_left (wrap_err "norm_term") uu____3052
  
let refine_intro : unit -> unit tac =
  fun uu____3129  ->
    let uu____3132 =
      let uu____3135 = cur_goal ()  in
      bind uu____3135
        (fun g  ->
           let uu____3142 =
             FStar_TypeChecker_Rel.base_and_refinement
               g.FStar_Tactics_Types.context g.FStar_Tactics_Types.goal_ty
              in
           match uu____3142 with
           | (uu____3155,FStar_Pervasives_Native.None ) ->
               fail "not a refinement"
           | (t,FStar_Pervasives_Native.Some (bv,phi)) ->
               let g1 =
                 let uu___94_3180 = g  in
                 {
                   FStar_Tactics_Types.context =
                     (uu___94_3180.FStar_Tactics_Types.context);
                   FStar_Tactics_Types.witness =
                     (uu___94_3180.FStar_Tactics_Types.witness);
                   FStar_Tactics_Types.goal_ty = t;
                   FStar_Tactics_Types.opts =
                     (uu___94_3180.FStar_Tactics_Types.opts);
                   FStar_Tactics_Types.is_guard =
                     (uu___94_3180.FStar_Tactics_Types.is_guard)
                 }  in
               let uu____3181 =
                 let uu____3186 =
                   let uu____3191 =
                     let uu____3192 = FStar_Syntax_Syntax.mk_binder bv  in
                     [uu____3192]  in
                   FStar_Syntax_Subst.open_term uu____3191 phi  in
                 match uu____3186 with
                 | (bvs,phi1) ->
                     let uu____3199 =
                       let uu____3200 = FStar_List.hd bvs  in
                       FStar_Pervasives_Native.fst uu____3200  in
                     (uu____3199, phi1)
                  in
               (match uu____3181 with
                | (bv1,phi1) ->
                    let uu____3213 =
                      let uu____3216 =
                        FStar_Syntax_Subst.subst
                          [FStar_Syntax_Syntax.NT
                             (bv1, (g.FStar_Tactics_Types.witness))] phi1
                         in
                      mk_irrelevant_goal "refine_intro refinement"
                        g.FStar_Tactics_Types.context uu____3216
                        g.FStar_Tactics_Types.opts
                       in
                    bind uu____3213
                      (fun g2  ->
                         bind __dismiss
                           (fun uu____3220  -> add_goals [g1; g2]))))
       in
    FStar_All.pipe_left (wrap_err "refine_intro") uu____3132
  
let __exact_now : Prims.bool -> FStar_Syntax_Syntax.term -> unit tac =
  fun set_expected_typ1  ->
    fun t  ->
      let uu____3239 = cur_goal ()  in
      bind uu____3239
        (fun goal  ->
           let env =
             if set_expected_typ1
             then
               FStar_TypeChecker_Env.set_expected_typ
                 goal.FStar_Tactics_Types.context
                 goal.FStar_Tactics_Types.goal_ty
             else goal.FStar_Tactics_Types.context  in
           let uu____3248 = __tc env t  in
           bind uu____3248
             (fun uu____3267  ->
                match uu____3267 with
                | (t1,typ,guard) ->
                    mlog
                      (fun uu____3282  ->
                         let uu____3283 =
                           tts goal.FStar_Tactics_Types.context typ  in
                         let uu____3284 =
                           FStar_TypeChecker_Rel.guard_to_string
                             goal.FStar_Tactics_Types.context guard
                            in
                         FStar_Util.print2
                           "__exact_now: got type %s\n__exact_now and guard %s\n"
                           uu____3283 uu____3284)
                      (fun uu____3287  ->
                         let uu____3288 =
                           proc_guard "__exact typing"
                             goal.FStar_Tactics_Types.context guard
                             goal.FStar_Tactics_Types.opts
                            in
                         bind uu____3288
                           (fun uu____3292  ->
                              mlog
                                (fun uu____3296  ->
                                   let uu____3297 =
                                     tts goal.FStar_Tactics_Types.context typ
                                      in
                                   let uu____3298 =
                                     tts goal.FStar_Tactics_Types.context
                                       goal.FStar_Tactics_Types.goal_ty
                                      in
                                   FStar_Util.print2
                                     "__exact_now: unifying %s and %s\n"
                                     uu____3297 uu____3298)
                                (fun uu____3301  ->
                                   let uu____3302 =
                                     do_unify
                                       goal.FStar_Tactics_Types.context typ
                                       goal.FStar_Tactics_Types.goal_ty
                                      in
                                   bind uu____3302
                                     (fun b  ->
                                        if b
                                        then solve goal t1
                                        else
                                          (let uu____3310 =
                                             tts
                                               goal.FStar_Tactics_Types.context
                                               t1
                                              in
                                           let uu____3311 =
                                             tts
                                               goal.FStar_Tactics_Types.context
                                               typ
                                              in
                                           let uu____3312 =
                                             tts
                                               goal.FStar_Tactics_Types.context
                                               goal.FStar_Tactics_Types.goal_ty
                                              in
                                           let uu____3313 =
                                             tts
                                               goal.FStar_Tactics_Types.context
                                               goal.FStar_Tactics_Types.witness
                                              in
                                           fail4
                                             "%s : %s does not exactly solve the goal %s (witness = %s)"
                                             uu____3310 uu____3311 uu____3312
                                             uu____3313)))))))
  
let t_exact : Prims.bool -> FStar_Syntax_Syntax.term -> unit tac =
  fun set_expected_typ1  ->
    fun tm  ->
      let uu____3328 =
        mlog
          (fun uu____3333  ->
             let uu____3334 = FStar_Syntax_Print.term_to_string tm  in
             FStar_Util.print1 "t_exact: tm = %s\n" uu____3334)
          (fun uu____3337  ->
             let uu____3338 =
               let uu____3345 = __exact_now set_expected_typ1 tm  in
               trytac' uu____3345  in
             bind uu____3338
               (fun uu___60_3354  ->
                  match uu___60_3354 with
                  | FStar_Util.Inr r -> ret ()
                  | FStar_Util.Inl e ->
                      let uu____3363 =
                        let uu____3370 =
                          let uu____3373 =
                            norm [FStar_Syntax_Embeddings.Delta]  in
                          bind uu____3373
                            (fun uu____3378  ->
                               let uu____3379 = refine_intro ()  in
                               bind uu____3379
                                 (fun uu____3383  ->
                                    __exact_now set_expected_typ1 tm))
                           in
                        trytac' uu____3370  in
                      bind uu____3363
                        (fun uu___59_3390  ->
                           match uu___59_3390 with
                           | FStar_Util.Inr r -> ret ()
                           | FStar_Util.Inl uu____3398 -> fail e)))
         in
      FStar_All.pipe_left (wrap_err "exact") uu____3328
  
let uvar_free_in_goal :
  FStar_Syntax_Syntax.uvar -> FStar_Tactics_Types.goal -> Prims.bool =
  fun u  ->
    fun g  ->
      if g.FStar_Tactics_Types.is_guard
      then false
      else
        (let free_uvars =
           let uu____3417 =
             let uu____3424 =
               FStar_Syntax_Free.uvars g.FStar_Tactics_Types.goal_ty  in
             FStar_Util.set_elements uu____3424  in
           FStar_List.map FStar_Pervasives_Native.fst uu____3417  in
         FStar_List.existsML (FStar_Syntax_Unionfind.equiv u) free_uvars)
  
let uvar_free :
  FStar_Syntax_Syntax.uvar -> FStar_Tactics_Types.proofstate -> Prims.bool =
  fun u  ->
    fun ps  ->
      FStar_List.existsML (uvar_free_in_goal u) ps.FStar_Tactics_Types.goals
  
let rec mapM : 'a 'b . ('a -> 'b tac) -> 'a Prims.list -> 'b Prims.list tac =
  fun f  ->
    fun l  ->
      match l with
      | [] -> ret []
      | x::xs ->
          let uu____3494 = f x  in
          bind uu____3494
            (fun y  ->
               let uu____3502 = mapM f xs  in
               bind uu____3502 (fun ys  -> ret (y :: ys)))
  
exception NoUnif 
let uu___is_NoUnif : Prims.exn -> Prims.bool =
  fun projectee  ->
    match projectee with | NoUnif  -> true | uu____3522 -> false
  
let rec __apply :
  Prims.bool ->
    FStar_Syntax_Syntax.term -> FStar_Reflection_Data.typ -> unit tac
  =
  fun uopt  ->
    fun tm  ->
      fun typ  ->
        let uu____3542 = cur_goal ()  in
        bind uu____3542
          (fun goal  ->
             mlog
               (fun uu____3549  ->
                  let uu____3550 = FStar_Syntax_Print.term_to_string tm  in
                  FStar_Util.print1 ">>> Calling __exact(%s)\n" uu____3550)
               (fun uu____3553  ->
                  let uu____3554 =
                    let uu____3559 =
                      let uu____3562 = t_exact false tm  in
                      with_policy FStar_Tactics_Types.Force uu____3562  in
                    trytac_exn uu____3559  in
                  bind uu____3554
                    (fun uu___61_3569  ->
                       match uu___61_3569 with
                       | FStar_Pervasives_Native.Some r -> ret ()
                       | FStar_Pervasives_Native.None  ->
                           mlog
                             (fun uu____3577  ->
                                let uu____3578 =
                                  FStar_Syntax_Print.term_to_string typ  in
                                FStar_Util.print1 ">>> typ = %s\n" uu____3578)
                             (fun uu____3581  ->
                                let uu____3582 =
                                  FStar_Syntax_Util.arrow_one typ  in
                                match uu____3582 with
                                | FStar_Pervasives_Native.None  ->
                                    FStar_Exn.raise NoUnif
                                | FStar_Pervasives_Native.Some ((bv,aq),c) ->
                                    mlog
                                      (fun uu____3614  ->
                                         let uu____3615 =
                                           FStar_Syntax_Print.binder_to_string
                                             (bv, aq)
                                            in
                                         FStar_Util.print1
                                           "__apply: pushing binder %s\n"
                                           uu____3615)
                                      (fun uu____3618  ->
                                         let uu____3619 =
                                           let uu____3620 =
                                             FStar_Syntax_Util.is_total_comp
                                               c
                                              in
                                           Prims.op_Negation uu____3620  in
                                         if uu____3619
                                         then
                                           fail "apply: not total codomain"
                                         else
                                           (let uu____3624 =
                                              new_uvar "apply"
                                                goal.FStar_Tactics_Types.context
                                                bv.FStar_Syntax_Syntax.sort
                                               in
                                            bind uu____3624
                                              (fun u  ->
                                                 let tm' =
                                                   FStar_Syntax_Syntax.mk_Tm_app
                                                     tm [(u, aq)]
                                                     FStar_Pervasives_Native.None
                                                     tm.FStar_Syntax_Syntax.pos
                                                    in
                                                 let typ' =
                                                   let uu____3644 =
                                                     comp_to_typ c  in
                                                   FStar_All.pipe_left
                                                     (FStar_Syntax_Subst.subst
                                                        [FStar_Syntax_Syntax.NT
                                                           (bv, u)])
                                                     uu____3644
                                                    in
                                                 let uu____3645 =
                                                   __apply uopt tm' typ'  in
                                                 bind uu____3645
                                                   (fun uu____3653  ->
                                                      let u1 =
                                                        bnorm
                                                          goal.FStar_Tactics_Types.context
                                                          u
                                                         in
                                                      let uu____3655 =
                                                        let uu____3656 =
                                                          let uu____3659 =
                                                            let uu____3660 =
                                                              FStar_Syntax_Util.head_and_args
                                                                u1
                                                               in
                                                            FStar_Pervasives_Native.fst
                                                              uu____3660
                                                             in
                                                          FStar_Syntax_Subst.compress
                                                            uu____3659
                                                           in
                                                        uu____3656.FStar_Syntax_Syntax.n
                                                         in
                                                      match uu____3655 with
                                                      | FStar_Syntax_Syntax.Tm_uvar
                                                          (uvar,uu____3688)
                                                          ->
                                                          bind get
                                                            (fun ps  ->
                                                               let uu____3716
                                                                 =
                                                                 uopt &&
                                                                   (uvar_free
                                                                    uvar ps)
                                                                  in
                                                               if uu____3716
                                                               then ret ()
                                                               else
                                                                 (let uu____3720
                                                                    =
                                                                    let uu____3723
                                                                    =
                                                                    let uu___95_3724
                                                                    = goal
                                                                     in
                                                                    let uu____3725
                                                                    =
                                                                    bnorm
                                                                    goal.FStar_Tactics_Types.context
                                                                    u1  in
                                                                    let uu____3726
                                                                    =
                                                                    bnorm
                                                                    goal.FStar_Tactics_Types.context
                                                                    bv.FStar_Syntax_Syntax.sort
                                                                     in
                                                                    {
                                                                    FStar_Tactics_Types.context
                                                                    =
                                                                    (uu___95_3724.FStar_Tactics_Types.context);
                                                                    FStar_Tactics_Types.witness
                                                                    =
                                                                    uu____3725;
                                                                    FStar_Tactics_Types.goal_ty
                                                                    =
                                                                    uu____3726;
                                                                    FStar_Tactics_Types.opts
                                                                    =
                                                                    (uu___95_3724.FStar_Tactics_Types.opts);
                                                                    FStar_Tactics_Types.is_guard
                                                                    = false
                                                                    }  in
                                                                    [uu____3723]
                                                                     in
                                                                  add_goals
                                                                    uu____3720))
                                                      | t -> ret ()))))))))
  
let try_unif : 'a . 'a tac -> 'a tac -> 'a tac =
  fun t  ->
    fun t'  -> mk_tac (fun ps  -> try run t ps with | NoUnif  -> run t' ps)
  
let apply : Prims.bool -> FStar_Syntax_Syntax.term -> unit tac =
  fun uopt  ->
    fun tm  ->
      let uu____3781 =
        mlog
          (fun uu____3786  ->
             let uu____3787 = FStar_Syntax_Print.term_to_string tm  in
             FStar_Util.print1 "apply: tm = %s\n" uu____3787)
          (fun uu____3790  ->
             let uu____3791 = cur_goal ()  in
             bind uu____3791
               (fun goal  ->
                  let uu____3797 = __tc goal.FStar_Tactics_Types.context tm
                     in
                  bind uu____3797
                    (fun uu____3819  ->
                       match uu____3819 with
                       | (tm1,typ,guard) ->
                           let typ1 =
                             bnorm goal.FStar_Tactics_Types.context typ  in
                           let uu____3832 =
                             let uu____3835 =
                               let uu____3838 = __apply uopt tm1 typ1  in
                               bind uu____3838
                                 (fun uu____3842  ->
                                    proc_guard "apply guard"
                                      goal.FStar_Tactics_Types.context guard
                                      goal.FStar_Tactics_Types.opts)
                                in
                             focus uu____3835  in
                           let uu____3843 =
                             let uu____3846 =
                               tts goal.FStar_Tactics_Types.context tm1  in
                             let uu____3847 =
                               tts goal.FStar_Tactics_Types.context typ1  in
                             let uu____3848 =
                               tts goal.FStar_Tactics_Types.context
                                 goal.FStar_Tactics_Types.goal_ty
                                in
                             fail3
                               "Cannot instantiate %s (of type %s) to match goal (%s)"
                               uu____3846 uu____3847 uu____3848
                              in
                           try_unif uu____3832 uu____3843)))
         in
      FStar_All.pipe_left (wrap_err "apply") uu____3781
  
let lemma_or_sq :
  FStar_Syntax_Syntax.comp ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun c  ->
    let ct = FStar_Syntax_Util.comp_to_comp_typ_nouniv c  in
    let uu____3871 =
      FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
        FStar_Parser_Const.effect_Lemma_lid
       in
    if uu____3871
    then
      let uu____3878 =
        match ct.FStar_Syntax_Syntax.effect_args with
        | pre::post::uu____3897 ->
            ((FStar_Pervasives_Native.fst pre),
              (FStar_Pervasives_Native.fst post))
        | uu____3938 -> failwith "apply_lemma: impossible: not a lemma"  in
      match uu____3878 with
      | (pre,post) ->
          let post1 =
            let uu____3974 =
              let uu____3983 =
                FStar_Syntax_Syntax.as_arg FStar_Syntax_Util.exp_unit  in
              [uu____3983]  in
            FStar_Syntax_Util.mk_app post uu____3974  in
          FStar_Pervasives_Native.Some (pre, post1)
    else
      (let uu____3997 =
         FStar_Syntax_Util.is_pure_effect ct.FStar_Syntax_Syntax.effect_name
          in
       if uu____3997
       then
         let uu____4004 =
           FStar_Syntax_Util.un_squash ct.FStar_Syntax_Syntax.result_typ  in
         FStar_Util.map_opt uu____4004
           (fun post  -> (FStar_Syntax_Util.t_true, post))
       else FStar_Pervasives_Native.None)
  
let apply_lemma : FStar_Syntax_Syntax.term -> unit tac =
  fun tm  ->
    let uu____4037 =
      let uu____4040 =
        mlog
          (fun uu____4045  ->
             let uu____4046 = FStar_Syntax_Print.term_to_string tm  in
             FStar_Util.print1 "apply_lemma: tm = %s\n" uu____4046)
          (fun uu____4050  ->
             let is_unit_t t =
               let uu____4057 =
                 let uu____4058 = FStar_Syntax_Subst.compress t  in
                 uu____4058.FStar_Syntax_Syntax.n  in
               match uu____4057 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.unit_lid
                   -> true
               | uu____4062 -> false  in
             let uu____4063 = cur_goal ()  in
             bind uu____4063
               (fun goal  ->
                  let uu____4069 = __tc goal.FStar_Tactics_Types.context tm
                     in
                  bind uu____4069
                    (fun uu____4092  ->
                       match uu____4092 with
                       | (tm1,t,guard) ->
                           let uu____4104 =
                             FStar_Syntax_Util.arrow_formals_comp t  in
                           (match uu____4104 with
                            | (bs,comp) ->
                                let uu____4131 = lemma_or_sq comp  in
                                (match uu____4131 with
                                 | FStar_Pervasives_Native.None  ->
                                     fail "not a lemma or squashed function"
                                 | FStar_Pervasives_Native.Some (pre,post) ->
                                     let uu____4150 =
                                       FStar_List.fold_left
                                         (fun uu____4196  ->
                                            fun uu____4197  ->
                                              match (uu____4196, uu____4197)
                                              with
                                              | ((uvs,guard1,subst1),(b,aq))
                                                  ->
                                                  let b_t =
                                                    FStar_Syntax_Subst.subst
                                                      subst1
                                                      b.FStar_Syntax_Syntax.sort
                                                     in
                                                  let uu____4300 =
                                                    is_unit_t b_t  in
                                                  if uu____4300
                                                  then
                                                    (((FStar_Syntax_Util.exp_unit,
                                                        aq) :: uvs), guard1,
                                                      ((FStar_Syntax_Syntax.NT
                                                          (b,
                                                            FStar_Syntax_Util.exp_unit))
                                                      :: subst1))
                                                  else
                                                    (let uu____4338 =
                                                       FStar_TypeChecker_Util.new_implicit_var
                                                         "apply_lemma"
                                                         (goal.FStar_Tactics_Types.goal_ty).FStar_Syntax_Syntax.pos
                                                         goal.FStar_Tactics_Types.context
                                                         b_t
                                                        in
                                                     match uu____4338 with
                                                     | (u,uu____4368,g_u) ->
                                                         let uu____4382 =
                                                           FStar_TypeChecker_Rel.conj_guard
                                                             guard1 g_u
                                                            in
                                                         (((u, aq) :: uvs),
                                                           uu____4382,
                                                           ((FStar_Syntax_Syntax.NT
                                                               (b, u)) ::
                                                           subst1))))
                                         ([], guard, []) bs
                                        in
                                     (match uu____4150 with
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
                                          let uu____4453 =
                                            let uu____4456 =
                                              FStar_Syntax_Util.mk_squash
                                                FStar_Syntax_Syntax.U_zero
                                                post1
                                               in
                                            do_unify
                                              goal.FStar_Tactics_Types.context
                                              uu____4456
                                              goal.FStar_Tactics_Types.goal_ty
                                             in
                                          bind uu____4453
                                            (fun b  ->
                                               if Prims.op_Negation b
                                               then
                                                 let uu____4464 =
                                                   tts
                                                     goal.FStar_Tactics_Types.context
                                                     tm1
                                                    in
                                                 let uu____4465 =
                                                   let uu____4466 =
                                                     FStar_Syntax_Util.mk_squash
                                                       FStar_Syntax_Syntax.U_zero
                                                       post1
                                                      in
                                                   tts
                                                     goal.FStar_Tactics_Types.context
                                                     uu____4466
                                                    in
                                                 let uu____4467 =
                                                   tts
                                                     goal.FStar_Tactics_Types.context
                                                     goal.FStar_Tactics_Types.goal_ty
                                                    in
                                                 fail3
                                                   "Cannot instantiate lemma %s (with postcondition: %s) to match goal (%s)"
                                                   uu____4464 uu____4465
                                                   uu____4467
                                               else
                                                 (let uu____4469 =
                                                    add_implicits
                                                      implicits.FStar_TypeChecker_Env.implicits
                                                     in
                                                  bind uu____4469
                                                    (fun uu____4474  ->
                                                       let uu____4475 =
                                                         solve goal
                                                           FStar_Syntax_Util.exp_unit
                                                          in
                                                       bind uu____4475
                                                         (fun uu____4483  ->
                                                            let is_free_uvar
                                                              uv t1 =
                                                              let free_uvars
                                                                =
                                                                let uu____4498
                                                                  =
                                                                  let uu____4505
                                                                    =
                                                                    FStar_Syntax_Free.uvars
                                                                    t1  in
                                                                  FStar_Util.set_elements
                                                                    uu____4505
                                                                   in
                                                                FStar_List.map
                                                                  FStar_Pervasives_Native.fst
                                                                  uu____4498
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
                                                              let uu____4554
                                                                =
                                                                FStar_Syntax_Util.head_and_args
                                                                  t1
                                                                 in
                                                              match uu____4554
                                                              with
                                                              | (hd1,uu____4570)
                                                                  ->
                                                                  (match 
                                                                    hd1.FStar_Syntax_Syntax.n
                                                                   with
                                                                   | 
                                                                   FStar_Syntax_Syntax.Tm_uvar
                                                                    (uv,uu____4592)
                                                                    ->
                                                                    appears
                                                                    uv goals
                                                                   | 
                                                                   uu____4617
                                                                    -> false)
                                                               in
                                                            let uu____4618 =
                                                              FStar_All.pipe_right
                                                                implicits.FStar_TypeChecker_Env.implicits
                                                                (mapM
                                                                   (fun
                                                                    uu____4690
                                                                     ->
                                                                    match uu____4690
                                                                    with
                                                                    | 
                                                                    (_msg,env,_uvar,term,typ,uu____4718)
                                                                    ->
                                                                    let uu____4719
                                                                    =
                                                                    FStar_Syntax_Util.head_and_args
                                                                    term  in
                                                                    (match uu____4719
                                                                    with
                                                                    | 
                                                                    (hd1,uu____4745)
                                                                    ->
                                                                    let uu____4766
                                                                    =
                                                                    let uu____4767
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    hd1  in
                                                                    uu____4767.FStar_Syntax_Syntax.n
                                                                     in
                                                                    (match uu____4766
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Tm_uvar
                                                                    uu____4780
                                                                    ->
                                                                    let uu____4797
                                                                    =
                                                                    let uu____4806
                                                                    =
                                                                    let uu____4809
                                                                    =
                                                                    let uu___98_4810
                                                                    = goal
                                                                     in
                                                                    let uu____4811
                                                                    =
                                                                    bnorm
                                                                    goal.FStar_Tactics_Types.context
                                                                    term  in
                                                                    let uu____4812
                                                                    =
                                                                    bnorm
                                                                    goal.FStar_Tactics_Types.context
                                                                    typ  in
                                                                    {
                                                                    FStar_Tactics_Types.context
                                                                    =
                                                                    (uu___98_4810.FStar_Tactics_Types.context);
                                                                    FStar_Tactics_Types.witness
                                                                    =
                                                                    uu____4811;
                                                                    FStar_Tactics_Types.goal_ty
                                                                    =
                                                                    uu____4812;
                                                                    FStar_Tactics_Types.opts
                                                                    =
                                                                    (uu___98_4810.FStar_Tactics_Types.opts);
                                                                    FStar_Tactics_Types.is_guard
                                                                    =
                                                                    (uu___98_4810.FStar_Tactics_Types.is_guard)
                                                                    }  in
                                                                    [uu____4809]
                                                                     in
                                                                    (uu____4806,
                                                                    [])  in
                                                                    ret
                                                                    uu____4797
                                                                    | 
                                                                    uu____4825
                                                                    ->
                                                                    let g_typ
                                                                    =
                                                                    let uu____4827
                                                                    =
                                                                    FStar_Options.__temp_fast_implicits
                                                                    ()  in
                                                                    if
                                                                    uu____4827
                                                                    then
                                                                    FStar_TypeChecker_TcTerm.check_type_of_well_typed_term
                                                                    false env
                                                                    term typ
                                                                    else
                                                                    (let term1
                                                                    =
                                                                    bnorm env
                                                                    term  in
                                                                    let uu____4830
                                                                    =
                                                                    let uu____4837
                                                                    =
                                                                    FStar_TypeChecker_Env.set_expected_typ
                                                                    env typ
                                                                     in
                                                                    env.FStar_TypeChecker_Env.type_of
                                                                    uu____4837
                                                                    term1  in
                                                                    match uu____4830
                                                                    with
                                                                    | 
                                                                    (uu____4838,uu____4839,g_typ)
                                                                    -> g_typ)
                                                                     in
                                                                    let uu____4841
                                                                    =
                                                                    goal_from_guard
                                                                    "apply_lemma solved arg"
                                                                    goal.FStar_Tactics_Types.context
                                                                    g_typ
                                                                    goal.FStar_Tactics_Types.opts
                                                                     in
                                                                    bind
                                                                    uu____4841
                                                                    (fun
                                                                    uu___62_4857
                                                                     ->
                                                                    match uu___62_4857
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
                                                            bind uu____4618
                                                              (fun goals_  ->
                                                                 let sub_goals
                                                                   =
                                                                   let uu____4925
                                                                    =
                                                                    FStar_List.map
                                                                    FStar_Pervasives_Native.fst
                                                                    goals_
                                                                     in
                                                                   FStar_List.flatten
                                                                    uu____4925
                                                                    in
                                                                 let smt_goals
                                                                   =
                                                                   let uu____4947
                                                                    =
                                                                    FStar_List.map
                                                                    FStar_Pervasives_Native.snd
                                                                    goals_
                                                                     in
                                                                   FStar_List.flatten
                                                                    uu____4947
                                                                    in
                                                                 let rec filter'
                                                                   f xs =
                                                                   match xs
                                                                   with
                                                                   | 
                                                                   [] -> []
                                                                   | 
                                                                   x::xs1 ->
                                                                    let uu____5008
                                                                    = f x xs1
                                                                     in
                                                                    if
                                                                    uu____5008
                                                                    then
                                                                    let uu____5011
                                                                    =
                                                                    filter' f
                                                                    xs1  in x
                                                                    ::
                                                                    uu____5011
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
                                                                    let uu____5025
                                                                    =
                                                                    checkone
                                                                    g.FStar_Tactics_Types.witness
                                                                    goals  in
                                                                    Prims.op_Negation
                                                                    uu____5025)
                                                                    sub_goals
                                                                    in
                                                                 let uu____5026
                                                                   =
                                                                   proc_guard
                                                                    "apply_lemma guard"
                                                                    goal.FStar_Tactics_Types.context
                                                                    guard
                                                                    goal.FStar_Tactics_Types.opts
                                                                    in
                                                                 bind
                                                                   uu____5026
                                                                   (fun
                                                                    uu____5031
                                                                     ->
                                                                    let uu____5032
                                                                    =
                                                                    let uu____5035
                                                                    =
                                                                    let uu____5036
                                                                    =
                                                                    let uu____5037
                                                                    =
                                                                    FStar_Syntax_Util.mk_squash
                                                                    FStar_Syntax_Syntax.U_zero
                                                                    pre1  in
                                                                    istrivial
                                                                    goal.FStar_Tactics_Types.context
                                                                    uu____5037
                                                                     in
                                                                    Prims.op_Negation
                                                                    uu____5036
                                                                     in
                                                                    if
                                                                    uu____5035
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
                                                                    uu____5032
                                                                    (fun
                                                                    uu____5043
                                                                     ->
                                                                    let uu____5044
                                                                    =
                                                                    add_smt_goals
                                                                    smt_goals
                                                                     in
                                                                    bind
                                                                    uu____5044
                                                                    (fun
                                                                    uu____5048
                                                                     ->
                                                                    add_goals
                                                                    sub_goals1))))))))))))))
         in
      focus uu____4040  in
    FStar_All.pipe_left (wrap_err "apply_lemma") uu____4037
  
let destruct_eq' :
  FStar_Reflection_Data.typ ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun typ  ->
    let uu____5070 = FStar_Syntax_Util.destruct_typ_as_formula typ  in
    match uu____5070 with
    | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn
        (l,uu____5080::(e1,uu____5082)::(e2,uu____5084)::[])) when
        FStar_Ident.lid_equals l FStar_Parser_Const.eq2_lid ->
        FStar_Pervasives_Native.Some (e1, e2)
    | uu____5143 -> FStar_Pervasives_Native.None
  
let destruct_eq :
  FStar_Reflection_Data.typ ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun typ  ->
    let uu____5167 = destruct_eq' typ  in
    match uu____5167 with
    | FStar_Pervasives_Native.Some t -> FStar_Pervasives_Native.Some t
    | FStar_Pervasives_Native.None  ->
        let uu____5197 = FStar_Syntax_Util.un_squash typ  in
        (match uu____5197 with
         | FStar_Pervasives_Native.Some typ1 -> destruct_eq' typ1
         | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None)
  
let split_env :
  FStar_Syntax_Syntax.bv ->
    env ->
      (env,FStar_Syntax_Syntax.bv Prims.list) FStar_Pervasives_Native.tuple2
        FStar_Pervasives_Native.option
  =
  fun bvar  ->
    fun e  ->
      let rec aux e1 =
        let uu____5259 = FStar_TypeChecker_Env.pop_bv e1  in
        match uu____5259 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (bv',e') ->
            if FStar_Syntax_Syntax.bv_eq bvar bv'
            then FStar_Pervasives_Native.Some (e', [])
            else
              (let uu____5307 = aux e'  in
               FStar_Util.map_opt uu____5307
                 (fun uu____5331  ->
                    match uu____5331 with | (e'',bvs) -> (e'', (bv' :: bvs))))
         in
      let uu____5352 = aux e  in
      FStar_Util.map_opt uu____5352
        (fun uu____5376  ->
           match uu____5376 with | (e',bvs) -> (e', (FStar_List.rev bvs)))
  
let push_bvs :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.bv Prims.list -> FStar_TypeChecker_Env.env
  =
  fun e  ->
    fun bvs  ->
      FStar_List.fold_left
        (fun e1  -> fun b  -> FStar_TypeChecker_Env.push_bv e1 b) e bvs
  
let subst_goal :
  FStar_Syntax_Syntax.bv ->
    FStar_Syntax_Syntax.bv ->
      FStar_Syntax_Syntax.subst_elt Prims.list ->
        FStar_Tactics_Types.goal ->
          FStar_Tactics_Types.goal FStar_Pervasives_Native.option
  =
  fun b1  ->
    fun b2  ->
      fun s  ->
        fun g  ->
          let uu____5443 = split_env b1 g.FStar_Tactics_Types.context  in
          FStar_Util.map_opt uu____5443
            (fun uu____5467  ->
               match uu____5467 with
               | (e0,bvs) ->
                   let s1 bv =
                     let uu___99_5486 = bv  in
                     let uu____5487 =
                       FStar_Syntax_Subst.subst s bv.FStar_Syntax_Syntax.sort
                        in
                     {
                       FStar_Syntax_Syntax.ppname =
                         (uu___99_5486.FStar_Syntax_Syntax.ppname);
                       FStar_Syntax_Syntax.index =
                         (uu___99_5486.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort = uu____5487
                     }  in
                   let bvs1 = FStar_List.map s1 bvs  in
                   let c = push_bvs e0 (b2 :: bvs1)  in
                   let w =
                     FStar_Syntax_Subst.subst s g.FStar_Tactics_Types.witness
                      in
                   let t =
                     FStar_Syntax_Subst.subst s g.FStar_Tactics_Types.goal_ty
                      in
                   let uu___100_5496 = g  in
                   {
                     FStar_Tactics_Types.context = c;
                     FStar_Tactics_Types.witness = w;
                     FStar_Tactics_Types.goal_ty = t;
                     FStar_Tactics_Types.opts =
                       (uu___100_5496.FStar_Tactics_Types.opts);
                     FStar_Tactics_Types.is_guard =
                       (uu___100_5496.FStar_Tactics_Types.is_guard)
                   })
  
let rewrite : FStar_Syntax_Syntax.binder -> unit tac =
  fun h  ->
    let uu____5506 = cur_goal ()  in
    bind uu____5506
      (fun goal  ->
         let uu____5514 = h  in
         match uu____5514 with
         | (bv,uu____5518) ->
             mlog
               (fun uu____5522  ->
                  let uu____5523 = FStar_Syntax_Print.bv_to_string bv  in
                  let uu____5524 =
                    tts goal.FStar_Tactics_Types.context
                      bv.FStar_Syntax_Syntax.sort
                     in
                  FStar_Util.print2 "+++Rewrite %s : %s\n" uu____5523
                    uu____5524)
               (fun uu____5527  ->
                  let uu____5528 =
                    split_env bv goal.FStar_Tactics_Types.context  in
                  match uu____5528 with
                  | FStar_Pervasives_Native.None  ->
                      fail "rewrite: binder not found in environment"
                  | FStar_Pervasives_Native.Some (e0,bvs) ->
                      let uu____5557 =
                        destruct_eq bv.FStar_Syntax_Syntax.sort  in
                      (match uu____5557 with
                       | FStar_Pervasives_Native.Some (x,e) ->
                           let uu____5572 =
                             let uu____5573 = FStar_Syntax_Subst.compress x
                                in
                             uu____5573.FStar_Syntax_Syntax.n  in
                           (match uu____5572 with
                            | FStar_Syntax_Syntax.Tm_name x1 ->
                                let s = [FStar_Syntax_Syntax.NT (x1, e)]  in
                                let s1 bv1 =
                                  let uu___101_5588 = bv1  in
                                  let uu____5589 =
                                    FStar_Syntax_Subst.subst s
                                      bv1.FStar_Syntax_Syntax.sort
                                     in
                                  {
                                    FStar_Syntax_Syntax.ppname =
                                      (uu___101_5588.FStar_Syntax_Syntax.ppname);
                                    FStar_Syntax_Syntax.index =
                                      (uu___101_5588.FStar_Syntax_Syntax.index);
                                    FStar_Syntax_Syntax.sort = uu____5589
                                  }  in
                                let bvs1 = FStar_List.map s1 bvs  in
                                let uu____5595 =
                                  let uu___102_5596 = goal  in
                                  let uu____5597 = push_bvs e0 (bv :: bvs1)
                                     in
                                  let uu____5598 =
                                    FStar_Syntax_Subst.subst s
                                      goal.FStar_Tactics_Types.witness
                                     in
                                  let uu____5599 =
                                    FStar_Syntax_Subst.subst s
                                      goal.FStar_Tactics_Types.goal_ty
                                     in
                                  {
                                    FStar_Tactics_Types.context = uu____5597;
                                    FStar_Tactics_Types.witness = uu____5598;
                                    FStar_Tactics_Types.goal_ty = uu____5599;
                                    FStar_Tactics_Types.opts =
                                      (uu___102_5596.FStar_Tactics_Types.opts);
                                    FStar_Tactics_Types.is_guard =
                                      (uu___102_5596.FStar_Tactics_Types.is_guard)
                                  }  in
                                replace_cur uu____5595
                            | uu____5600 ->
                                fail
                                  "rewrite: Not an equality hypothesis with a variable on the LHS")
                       | uu____5601 ->
                           fail "rewrite: Not an equality hypothesis")))
  
let rename_to : FStar_Syntax_Syntax.binder -> Prims.string -> unit tac =
  fun b  ->
    fun s  ->
      let uu____5622 = cur_goal ()  in
      bind uu____5622
        (fun goal  ->
           let uu____5633 = b  in
           match uu____5633 with
           | (bv,uu____5637) ->
               let bv' =
                 let uu____5639 =
                   let uu___103_5640 = bv  in
                   let uu____5641 =
                     FStar_Ident.mk_ident
                       (s,
                         ((bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))
                      in
                   {
                     FStar_Syntax_Syntax.ppname = uu____5641;
                     FStar_Syntax_Syntax.index =
                       (uu___103_5640.FStar_Syntax_Syntax.index);
                     FStar_Syntax_Syntax.sort =
                       (uu___103_5640.FStar_Syntax_Syntax.sort)
                   }  in
                 FStar_Syntax_Syntax.freshen_bv uu____5639  in
               let s1 =
                 let uu____5645 =
                   let uu____5646 =
                     let uu____5653 = FStar_Syntax_Syntax.bv_to_name bv'  in
                     (bv, uu____5653)  in
                   FStar_Syntax_Syntax.NT uu____5646  in
                 [uu____5645]  in
               let uu____5654 = subst_goal bv bv' s1 goal  in
               (match uu____5654 with
                | FStar_Pervasives_Native.None  ->
                    fail "rename_to: binder not found in environment"
                | FStar_Pervasives_Native.Some goal1 -> replace_cur goal1))
  
let binder_retype : FStar_Syntax_Syntax.binder -> unit tac =
  fun b  ->
    let uu____5669 = cur_goal ()  in
    bind uu____5669
      (fun goal  ->
         let uu____5678 = b  in
         match uu____5678 with
         | (bv,uu____5682) ->
             let uu____5683 = split_env bv goal.FStar_Tactics_Types.context
                in
             (match uu____5683 with
              | FStar_Pervasives_Native.None  ->
                  fail "binder_retype: binder is not present in environment"
              | FStar_Pervasives_Native.Some (e0,bvs) ->
                  let uu____5712 = FStar_Syntax_Util.type_u ()  in
                  (match uu____5712 with
                   | (ty,u) ->
                       let uu____5721 = new_uvar "binder_retype" e0 ty  in
                       bind uu____5721
                         (fun t'  ->
                            let bv'' =
                              let uu___104_5731 = bv  in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___104_5731.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___104_5731.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = t'
                              }  in
                            let s =
                              let uu____5735 =
                                let uu____5736 =
                                  let uu____5743 =
                                    FStar_Syntax_Syntax.bv_to_name bv''  in
                                  (bv, uu____5743)  in
                                FStar_Syntax_Syntax.NT uu____5736  in
                              [uu____5735]  in
                            let bvs1 =
                              FStar_List.map
                                (fun b1  ->
                                   let uu___105_5751 = b1  in
                                   let uu____5752 =
                                     FStar_Syntax_Subst.subst s
                                       b1.FStar_Syntax_Syntax.sort
                                      in
                                   {
                                     FStar_Syntax_Syntax.ppname =
                                       (uu___105_5751.FStar_Syntax_Syntax.ppname);
                                     FStar_Syntax_Syntax.index =
                                       (uu___105_5751.FStar_Syntax_Syntax.index);
                                     FStar_Syntax_Syntax.sort = uu____5752
                                   }) bvs
                               in
                            let env' = push_bvs e0 (bv'' :: bvs1)  in
                            bind __dismiss
                              (fun uu____5758  ->
                                 let uu____5759 =
                                   let uu____5762 =
                                     let uu____5765 =
                                       let uu___106_5766 = goal  in
                                       let uu____5767 =
                                         FStar_Syntax_Subst.subst s
                                           goal.FStar_Tactics_Types.witness
                                          in
                                       let uu____5768 =
                                         FStar_Syntax_Subst.subst s
                                           goal.FStar_Tactics_Types.goal_ty
                                          in
                                       {
                                         FStar_Tactics_Types.context = env';
                                         FStar_Tactics_Types.witness =
                                           uu____5767;
                                         FStar_Tactics_Types.goal_ty =
                                           uu____5768;
                                         FStar_Tactics_Types.opts =
                                           (uu___106_5766.FStar_Tactics_Types.opts);
                                         FStar_Tactics_Types.is_guard =
                                           (uu___106_5766.FStar_Tactics_Types.is_guard)
                                       }  in
                                     [uu____5765]  in
                                   add_goals uu____5762  in
                                 bind uu____5759
                                   (fun uu____5771  ->
                                      let uu____5772 =
                                        FStar_Syntax_Util.mk_eq2
                                          (FStar_Syntax_Syntax.U_succ u) ty
                                          bv.FStar_Syntax_Syntax.sort t'
                                         in
                                      add_irrelevant_goal
                                        "binder_retype equation" e0
                                        uu____5772
                                        goal.FStar_Tactics_Types.opts))))))
  
let norm_binder_type :
  FStar_Syntax_Embeddings.norm_step Prims.list ->
    FStar_Syntax_Syntax.binder -> unit tac
  =
  fun s  ->
    fun b  ->
      let uu____5791 = cur_goal ()  in
      bind uu____5791
        (fun goal  ->
           let uu____5800 = b  in
           match uu____5800 with
           | (bv,uu____5804) ->
               let uu____5805 = split_env bv goal.FStar_Tactics_Types.context
                  in
               (match uu____5805 with
                | FStar_Pervasives_Native.None  ->
                    fail
                      "binder_retype: binder is not present in environment"
                | FStar_Pervasives_Native.Some (e0,bvs) ->
                    let steps =
                      let uu____5837 =
                        FStar_TypeChecker_Normalize.tr_norm_steps s  in
                      FStar_List.append
                        [FStar_TypeChecker_Normalize.Reify;
                        FStar_TypeChecker_Normalize.UnfoldTac] uu____5837
                       in
                    let sort' =
                      normalize steps e0 bv.FStar_Syntax_Syntax.sort  in
                    let bv' =
                      let uu___107_5842 = bv  in
                      {
                        FStar_Syntax_Syntax.ppname =
                          (uu___107_5842.FStar_Syntax_Syntax.ppname);
                        FStar_Syntax_Syntax.index =
                          (uu___107_5842.FStar_Syntax_Syntax.index);
                        FStar_Syntax_Syntax.sort = sort'
                      }  in
                    let env' = push_bvs e0 (bv' :: bvs)  in
                    replace_cur
                      (let uu___108_5846 = goal  in
                       {
                         FStar_Tactics_Types.context = env';
                         FStar_Tactics_Types.witness =
                           (uu___108_5846.FStar_Tactics_Types.witness);
                         FStar_Tactics_Types.goal_ty =
                           (uu___108_5846.FStar_Tactics_Types.goal_ty);
                         FStar_Tactics_Types.opts =
                           (uu___108_5846.FStar_Tactics_Types.opts);
                         FStar_Tactics_Types.is_guard =
                           (uu___108_5846.FStar_Tactics_Types.is_guard)
                       })))
  
let revert : unit -> unit tac =
  fun uu____5853  ->
    let uu____5856 = cur_goal ()  in
    bind uu____5856
      (fun goal  ->
         let uu____5862 =
           FStar_TypeChecker_Env.pop_bv goal.FStar_Tactics_Types.context  in
         match uu____5862 with
         | FStar_Pervasives_Native.None  ->
             fail "Cannot revert; empty context"
         | FStar_Pervasives_Native.Some (x,env') ->
             let typ' =
               let uu____5884 =
                 FStar_Syntax_Syntax.mk_Total
                   goal.FStar_Tactics_Types.goal_ty
                  in
               FStar_Syntax_Util.arrow [(x, FStar_Pervasives_Native.None)]
                 uu____5884
                in
             let w' =
               FStar_Syntax_Util.abs [(x, FStar_Pervasives_Native.None)]
                 goal.FStar_Tactics_Types.witness
                 FStar_Pervasives_Native.None
                in
             replace_cur
               (let uu___109_5918 = goal  in
                {
                  FStar_Tactics_Types.context = env';
                  FStar_Tactics_Types.witness = w';
                  FStar_Tactics_Types.goal_ty = typ';
                  FStar_Tactics_Types.opts =
                    (uu___109_5918.FStar_Tactics_Types.opts);
                  FStar_Tactics_Types.is_guard =
                    (uu___109_5918.FStar_Tactics_Types.is_guard)
                }))
  
let free_in :
  FStar_Syntax_Syntax.bv -> FStar_Syntax_Syntax.term -> Prims.bool =
  fun bv  ->
    fun t  ->
      let uu____5929 = FStar_Syntax_Free.names t  in
      FStar_Util.set_mem bv uu____5929
  
let rec clear : FStar_Syntax_Syntax.binder -> unit tac =
  fun b  ->
    let bv = FStar_Pervasives_Native.fst b  in
    let uu____5942 = cur_goal ()  in
    bind uu____5942
      (fun goal  ->
         mlog
           (fun uu____5950  ->
              let uu____5951 = FStar_Syntax_Print.binder_to_string b  in
              let uu____5952 =
                let uu____5953 =
                  let uu____5954 =
                    FStar_TypeChecker_Env.all_binders
                      goal.FStar_Tactics_Types.context
                     in
                  FStar_All.pipe_right uu____5954 FStar_List.length  in
                FStar_All.pipe_right uu____5953 FStar_Util.string_of_int  in
              FStar_Util.print2 "Clear of (%s), env has %s binders\n"
                uu____5951 uu____5952)
           (fun uu____5965  ->
              let uu____5966 = split_env bv goal.FStar_Tactics_Types.context
                 in
              match uu____5966 with
              | FStar_Pervasives_Native.None  ->
                  fail "Cannot clear; binder not in environment"
              | FStar_Pervasives_Native.Some (e',bvs) ->
                  let rec check1 bvs1 =
                    match bvs1 with
                    | [] -> ret ()
                    | bv'::bvs2 ->
                        let uu____6013 =
                          free_in bv bv'.FStar_Syntax_Syntax.sort  in
                        if uu____6013
                        then
                          let uu____6016 =
                            let uu____6017 =
                              FStar_Syntax_Print.bv_to_string bv'  in
                            FStar_Util.format1
                              "Cannot clear; binder present in the type of %s"
                              uu____6017
                             in
                          fail uu____6016
                        else check1 bvs2
                     in
                  let uu____6019 =
                    free_in bv goal.FStar_Tactics_Types.goal_ty  in
                  if uu____6019
                  then fail "Cannot clear; binder present in goal"
                  else
                    (let uu____6023 = check1 bvs  in
                     bind uu____6023
                       (fun uu____6029  ->
                          let env' = push_bvs e' bvs  in
                          let uu____6031 =
                            new_uvar "clear.witness" env'
                              goal.FStar_Tactics_Types.goal_ty
                             in
                          bind uu____6031
                            (fun ut  ->
                               let uu____6037 =
                                 do_unify goal.FStar_Tactics_Types.context
                                   goal.FStar_Tactics_Types.witness ut
                                  in
                               bind uu____6037
                                 (fun b1  ->
                                    if b1
                                    then
                                      replace_cur
                                        (let uu___110_6046 = goal  in
                                         {
                                           FStar_Tactics_Types.context = env';
                                           FStar_Tactics_Types.witness = ut;
                                           FStar_Tactics_Types.goal_ty =
                                             (uu___110_6046.FStar_Tactics_Types.goal_ty);
                                           FStar_Tactics_Types.opts =
                                             (uu___110_6046.FStar_Tactics_Types.opts);
                                           FStar_Tactics_Types.is_guard =
                                             (uu___110_6046.FStar_Tactics_Types.is_guard)
                                         })
                                    else
                                      fail
                                        "Cannot clear; binder appears in witness"))))))
  
let clear_top : unit -> unit tac =
  fun uu____6054  ->
    let uu____6057 = cur_goal ()  in
    bind uu____6057
      (fun goal  ->
         let uu____6063 =
           FStar_TypeChecker_Env.pop_bv goal.FStar_Tactics_Types.context  in
         match uu____6063 with
         | FStar_Pervasives_Native.None  ->
             fail "Cannot clear; empty context"
         | FStar_Pervasives_Native.Some (x,uu____6077) ->
             let uu____6082 = FStar_Syntax_Syntax.mk_binder x  in
             clear uu____6082)
  
let prune : Prims.string -> unit tac =
  fun s  ->
    let uu____6092 = cur_goal ()  in
    bind uu____6092
      (fun g  ->
         let ctx = g.FStar_Tactics_Types.context  in
         let ctx' =
           let uu____6102 = FStar_Ident.path_of_text s  in
           FStar_TypeChecker_Env.rem_proof_ns ctx uu____6102  in
         let g' =
           let uu___111_6104 = g  in
           {
             FStar_Tactics_Types.context = ctx';
             FStar_Tactics_Types.witness =
               (uu___111_6104.FStar_Tactics_Types.witness);
             FStar_Tactics_Types.goal_ty =
               (uu___111_6104.FStar_Tactics_Types.goal_ty);
             FStar_Tactics_Types.opts =
               (uu___111_6104.FStar_Tactics_Types.opts);
             FStar_Tactics_Types.is_guard =
               (uu___111_6104.FStar_Tactics_Types.is_guard)
           }  in
         bind __dismiss (fun uu____6106  -> add_goals [g']))
  
let addns : Prims.string -> unit tac =
  fun s  ->
    let uu____6116 = cur_goal ()  in
    bind uu____6116
      (fun g  ->
         let ctx = g.FStar_Tactics_Types.context  in
         let ctx' =
           let uu____6126 = FStar_Ident.path_of_text s  in
           FStar_TypeChecker_Env.add_proof_ns ctx uu____6126  in
         let g' =
           let uu___112_6128 = g  in
           {
             FStar_Tactics_Types.context = ctx';
             FStar_Tactics_Types.witness =
               (uu___112_6128.FStar_Tactics_Types.witness);
             FStar_Tactics_Types.goal_ty =
               (uu___112_6128.FStar_Tactics_Types.goal_ty);
             FStar_Tactics_Types.opts =
               (uu___112_6128.FStar_Tactics_Types.opts);
             FStar_Tactics_Types.is_guard =
               (uu___112_6128.FStar_Tactics_Types.is_guard)
           }  in
         bind __dismiss (fun uu____6130  -> add_goals [g']))
  
let rec tac_fold_env :
  FStar_Tactics_Types.direction ->
    (env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac) ->
      env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac
  =
  fun d  ->
    fun f  ->
      fun env  ->
        fun t  ->
          let tn =
            let uu____6170 = FStar_Syntax_Subst.compress t  in
            uu____6170.FStar_Syntax_Syntax.n  in
          let uu____6173 =
            if d = FStar_Tactics_Types.TopDown
            then
              f env
                (let uu___116_6179 = t  in
                 {
                   FStar_Syntax_Syntax.n = tn;
                   FStar_Syntax_Syntax.pos =
                     (uu___116_6179.FStar_Syntax_Syntax.pos);
                   FStar_Syntax_Syntax.vars =
                     (uu___116_6179.FStar_Syntax_Syntax.vars)
                 })
            else ret t  in
          bind uu____6173
            (fun t1  ->
               let ff = tac_fold_env d f env  in
               let tn1 =
                 let uu____6195 =
                   let uu____6196 = FStar_Syntax_Subst.compress t1  in
                   uu____6196.FStar_Syntax_Syntax.n  in
                 match uu____6195 with
                 | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
                     let uu____6223 = ff hd1  in
                     bind uu____6223
                       (fun hd2  ->
                          let fa uu____6245 =
                            match uu____6245 with
                            | (a,q) ->
                                let uu____6258 = ff a  in
                                bind uu____6258 (fun a1  -> ret (a1, q))
                             in
                          let uu____6271 = mapM fa args  in
                          bind uu____6271
                            (fun args1  ->
                               ret (FStar_Syntax_Syntax.Tm_app (hd2, args1))))
                 | FStar_Syntax_Syntax.Tm_abs (bs,t2,k) ->
                     let uu____6331 = FStar_Syntax_Subst.open_term bs t2  in
                     (match uu____6331 with
                      | (bs1,t') ->
                          let uu____6340 =
                            let uu____6343 =
                              FStar_TypeChecker_Env.push_binders env bs1  in
                            tac_fold_env d f uu____6343 t'  in
                          bind uu____6340
                            (fun t''  ->
                               let uu____6347 =
                                 let uu____6348 =
                                   let uu____6365 =
                                     FStar_Syntax_Subst.close_binders bs1  in
                                   let uu____6366 =
                                     FStar_Syntax_Subst.close bs1 t''  in
                                   (uu____6365, uu____6366, k)  in
                                 FStar_Syntax_Syntax.Tm_abs uu____6348  in
                               ret uu____6347))
                 | FStar_Syntax_Syntax.Tm_arrow (bs,k) -> ret tn
                 | FStar_Syntax_Syntax.Tm_match (hd1,brs) ->
                     let uu____6425 = ff hd1  in
                     bind uu____6425
                       (fun hd2  ->
                          let ffb br =
                            let uu____6440 =
                              FStar_Syntax_Subst.open_branch br  in
                            match uu____6440 with
                            | (pat,w,e) ->
                                let bvs = FStar_Syntax_Syntax.pat_bvs pat  in
                                let ff1 =
                                  let uu____6472 =
                                    FStar_TypeChecker_Env.push_bvs env bvs
                                     in
                                  tac_fold_env d f uu____6472  in
                                let uu____6473 = ff1 e  in
                                bind uu____6473
                                  (fun e1  ->
                                     let br1 =
                                       FStar_Syntax_Subst.close_branch
                                         (pat, w, e1)
                                        in
                                     ret br1)
                             in
                          let uu____6486 = mapM ffb brs  in
                          bind uu____6486
                            (fun brs1  ->
                               ret (FStar_Syntax_Syntax.Tm_match (hd2, brs1))))
                 | FStar_Syntax_Syntax.Tm_let
                     ((false
                       ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl bv;
                          FStar_Syntax_Syntax.lbunivs = uu____6500;
                          FStar_Syntax_Syntax.lbtyp = uu____6501;
                          FStar_Syntax_Syntax.lbeff = uu____6502;
                          FStar_Syntax_Syntax.lbdef = def;
                          FStar_Syntax_Syntax.lbattrs = uu____6504;
                          FStar_Syntax_Syntax.lbpos = uu____6505;_}::[]),e)
                     ->
                     let lb =
                       let uu____6530 =
                         let uu____6531 = FStar_Syntax_Subst.compress t1  in
                         uu____6531.FStar_Syntax_Syntax.n  in
                       match uu____6530 with
                       | FStar_Syntax_Syntax.Tm_let
                           ((false ,lb::[]),uu____6535) -> lb
                       | uu____6548 -> failwith "impossible"  in
                     let fflb lb1 =
                       let uu____6557 = ff lb1.FStar_Syntax_Syntax.lbdef  in
                       bind uu____6557
                         (fun def1  ->
                            ret
                              (let uu___113_6563 = lb1  in
                               {
                                 FStar_Syntax_Syntax.lbname =
                                   (uu___113_6563.FStar_Syntax_Syntax.lbname);
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___113_6563.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp =
                                   (uu___113_6563.FStar_Syntax_Syntax.lbtyp);
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___113_6563.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def1;
                                 FStar_Syntax_Syntax.lbattrs =
                                   (uu___113_6563.FStar_Syntax_Syntax.lbattrs);
                                 FStar_Syntax_Syntax.lbpos =
                                   (uu___113_6563.FStar_Syntax_Syntax.lbpos)
                               }))
                        in
                     let uu____6564 = fflb lb  in
                     bind uu____6564
                       (fun lb1  ->
                          let uu____6574 =
                            let uu____6579 =
                              let uu____6580 =
                                FStar_Syntax_Syntax.mk_binder bv  in
                              [uu____6580]  in
                            FStar_Syntax_Subst.open_term uu____6579 e  in
                          match uu____6574 with
                          | (bs,e1) ->
                              let ff1 =
                                let uu____6592 =
                                  FStar_TypeChecker_Env.push_binders env bs
                                   in
                                tac_fold_env d f uu____6592  in
                              let uu____6593 = ff1 e1  in
                              bind uu____6593
                                (fun e2  ->
                                   let e3 = FStar_Syntax_Subst.close bs e2
                                      in
                                   ret
                                     (FStar_Syntax_Syntax.Tm_let
                                        ((false, [lb1]), e3))))
                 | FStar_Syntax_Syntax.Tm_let ((true ,lbs),e) ->
                     let fflb lb =
                       let uu____6632 = ff lb.FStar_Syntax_Syntax.lbdef  in
                       bind uu____6632
                         (fun def  ->
                            ret
                              (let uu___114_6638 = lb  in
                               {
                                 FStar_Syntax_Syntax.lbname =
                                   (uu___114_6638.FStar_Syntax_Syntax.lbname);
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___114_6638.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp =
                                   (uu___114_6638.FStar_Syntax_Syntax.lbtyp);
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___114_6638.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def;
                                 FStar_Syntax_Syntax.lbattrs =
                                   (uu___114_6638.FStar_Syntax_Syntax.lbattrs);
                                 FStar_Syntax_Syntax.lbpos =
                                   (uu___114_6638.FStar_Syntax_Syntax.lbpos)
                               }))
                        in
                     let uu____6639 = FStar_Syntax_Subst.open_let_rec lbs e
                        in
                     (match uu____6639 with
                      | (lbs1,e1) ->
                          let uu____6654 = mapM fflb lbs1  in
                          bind uu____6654
                            (fun lbs2  ->
                               let uu____6666 = ff e1  in
                               bind uu____6666
                                 (fun e2  ->
                                    let uu____6674 =
                                      FStar_Syntax_Subst.close_let_rec lbs2
                                        e2
                                       in
                                    match uu____6674 with
                                    | (lbs3,e3) ->
                                        ret
                                          (FStar_Syntax_Syntax.Tm_let
                                             ((true, lbs3), e3)))))
                 | FStar_Syntax_Syntax.Tm_ascribed (t2,asc,eff) ->
                     let uu____6740 = ff t2  in
                     bind uu____6740
                       (fun t3  ->
                          ret
                            (FStar_Syntax_Syntax.Tm_ascribed (t3, asc, eff)))
                 | FStar_Syntax_Syntax.Tm_meta (t2,m) ->
                     let uu____6769 = ff t2  in
                     bind uu____6769
                       (fun t3  -> ret (FStar_Syntax_Syntax.Tm_meta (t3, m)))
                 | uu____6774 -> ret tn  in
               bind tn1
                 (fun tn2  ->
                    let t' =
                      let uu___115_6781 = t1  in
                      {
                        FStar_Syntax_Syntax.n = tn2;
                        FStar_Syntax_Syntax.pos =
                          (uu___115_6781.FStar_Syntax_Syntax.pos);
                        FStar_Syntax_Syntax.vars =
                          (uu___115_6781.FStar_Syntax_Syntax.vars)
                      }  in
                    if d = FStar_Tactics_Types.BottomUp
                    then f env t'
                    else ret t'))
  
let pointwise_rec :
  FStar_Tactics_Types.proofstate ->
    unit tac ->
      FStar_Options.optionstate ->
        FStar_TypeChecker_Env.env ->
          FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac
  =
  fun ps  ->
    fun tau  ->
      fun opts  ->
        fun env  ->
          fun t  ->
            let uu____6820 = FStar_TypeChecker_TcTerm.tc_term env t  in
            match uu____6820 with
            | (t1,lcomp,g) ->
                let uu____6832 =
                  (let uu____6835 =
                     FStar_Syntax_Util.is_pure_or_ghost_lcomp lcomp  in
                   Prims.op_Negation uu____6835) ||
                    (let uu____6837 = FStar_TypeChecker_Rel.is_trivial g  in
                     Prims.op_Negation uu____6837)
                   in
                if uu____6832
                then ret t1
                else
                  (let rewrite_eq =
                     let typ = lcomp.FStar_Syntax_Syntax.res_typ  in
                     let uu____6847 = new_uvar "pointwise_rec" env typ  in
                     bind uu____6847
                       (fun ut  ->
                          log ps
                            (fun uu____6858  ->
                               let uu____6859 =
                                 FStar_Syntax_Print.term_to_string t1  in
                               let uu____6860 =
                                 FStar_Syntax_Print.term_to_string ut  in
                               FStar_Util.print2
                                 "Pointwise_rec: making equality\n\t%s ==\n\t%s\n"
                                 uu____6859 uu____6860);
                          (let uu____6861 =
                             let uu____6864 =
                               let uu____6865 =
                                 FStar_TypeChecker_TcTerm.universe_of env typ
                                  in
                               FStar_Syntax_Util.mk_eq2 uu____6865 typ t1 ut
                                in
                             add_irrelevant_goal "pointwise_rec equation" env
                               uu____6864 opts
                              in
                           bind uu____6861
                             (fun uu____6868  ->
                                let uu____6869 =
                                  bind tau
                                    (fun uu____6875  ->
                                       let ut1 =
                                         FStar_TypeChecker_Normalize.reduce_uvar_solutions
                                           env ut
                                          in
                                       log ps
                                         (fun uu____6881  ->
                                            let uu____6882 =
                                              FStar_Syntax_Print.term_to_string
                                                t1
                                               in
                                            let uu____6883 =
                                              FStar_Syntax_Print.term_to_string
                                                ut1
                                               in
                                            FStar_Util.print2
                                              "Pointwise_rec: succeeded rewriting\n\t%s to\n\t%s\n"
                                              uu____6882 uu____6883);
                                       ret ut1)
                                   in
                                focus uu____6869)))
                      in
                   let uu____6884 = trytac' rewrite_eq  in
                   bind uu____6884
                     (fun x  ->
                        match x with
                        | FStar_Util.Inl "SKIP" -> ret t1
                        | FStar_Util.Inl e -> fail e
                        | FStar_Util.Inr x1 -> ret x1))
  
type ctrl = FStar_BigInt.t[@@deriving show]
let keepGoing : ctrl = FStar_BigInt.zero 
let proceedToNextSubtree : FStar_BigInt.bigint = FStar_BigInt.one 
let globalStop : FStar_BigInt.bigint =
  FStar_BigInt.succ_big_int FStar_BigInt.one 
type rewrite_result = Prims.bool[@@deriving show]
let skipThisTerm : Prims.bool = false 
let rewroteThisTerm : Prims.bool = true 
type 'a ctrl_tac = ('a,ctrl) FStar_Pervasives_Native.tuple2 tac[@@deriving
                                                                 show]
let rec ctrl_tac_fold :
  (env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term ctrl_tac) ->
    env ->
      ctrl -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term ctrl_tac
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
          let uu____7056 = FStar_Syntax_Subst.compress t  in
          maybe_continue ctrl uu____7056
            (fun t1  ->
               let uu____7060 =
                 f env
                   (let uu___119_7069 = t1  in
                    {
                      FStar_Syntax_Syntax.n = (t1.FStar_Syntax_Syntax.n);
                      FStar_Syntax_Syntax.pos =
                        (uu___119_7069.FStar_Syntax_Syntax.pos);
                      FStar_Syntax_Syntax.vars =
                        (uu___119_7069.FStar_Syntax_Syntax.vars)
                    })
                  in
               bind uu____7060
                 (fun uu____7081  ->
                    match uu____7081 with
                    | (t2,ctrl1) ->
                        maybe_continue ctrl1 t2
                          (fun t3  ->
                             let uu____7100 =
                               let uu____7101 =
                                 FStar_Syntax_Subst.compress t3  in
                               uu____7101.FStar_Syntax_Syntax.n  in
                             match uu____7100 with
                             | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
                                 let uu____7134 =
                                   ctrl_tac_fold f env ctrl1 hd1  in
                                 bind uu____7134
                                   (fun uu____7159  ->
                                      match uu____7159 with
                                      | (hd2,ctrl2) ->
                                          let ctrl3 = keep_going ctrl2  in
                                          let uu____7175 =
                                            ctrl_tac_fold_args f env ctrl3
                                              args
                                             in
                                          bind uu____7175
                                            (fun uu____7202  ->
                                               match uu____7202 with
                                               | (args1,ctrl4) ->
                                                   ret
                                                     ((let uu___117_7232 = t3
                                                          in
                                                       {
                                                         FStar_Syntax_Syntax.n
                                                           =
                                                           (FStar_Syntax_Syntax.Tm_app
                                                              (hd2, args1));
                                                         FStar_Syntax_Syntax.pos
                                                           =
                                                           (uu___117_7232.FStar_Syntax_Syntax.pos);
                                                         FStar_Syntax_Syntax.vars
                                                           =
                                                           (uu___117_7232.FStar_Syntax_Syntax.vars)
                                                       }), ctrl4)))
                             | FStar_Syntax_Syntax.Tm_abs (bs,t4,k) ->
                                 let uu____7258 =
                                   FStar_Syntax_Subst.open_term bs t4  in
                                 (match uu____7258 with
                                  | (bs1,t') ->
                                      let uu____7273 =
                                        let uu____7280 =
                                          FStar_TypeChecker_Env.push_binders
                                            env bs1
                                           in
                                        ctrl_tac_fold f uu____7280 ctrl1 t'
                                         in
                                      bind uu____7273
                                        (fun uu____7298  ->
                                           match uu____7298 with
                                           | (t'',ctrl2) ->
                                               let uu____7313 =
                                                 let uu____7320 =
                                                   let uu___118_7323 = t4  in
                                                   let uu____7326 =
                                                     let uu____7327 =
                                                       let uu____7344 =
                                                         FStar_Syntax_Subst.close_binders
                                                           bs1
                                                          in
                                                       let uu____7345 =
                                                         FStar_Syntax_Subst.close
                                                           bs1 t''
                                                          in
                                                       (uu____7344,
                                                         uu____7345, k)
                                                        in
                                                     FStar_Syntax_Syntax.Tm_abs
                                                       uu____7327
                                                      in
                                                   {
                                                     FStar_Syntax_Syntax.n =
                                                       uu____7326;
                                                     FStar_Syntax_Syntax.pos
                                                       =
                                                       (uu___118_7323.FStar_Syntax_Syntax.pos);
                                                     FStar_Syntax_Syntax.vars
                                                       =
                                                       (uu___118_7323.FStar_Syntax_Syntax.vars)
                                                   }  in
                                                 (uu____7320, ctrl2)  in
                                               ret uu____7313))
                             | FStar_Syntax_Syntax.Tm_arrow (bs,k) ->
                                 ret (t3, ctrl1)
                             | uu____7378 -> ret (t3, ctrl1))))

and ctrl_tac_fold_args :
  (env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term ctrl_tac) ->
    env ->
      ctrl ->
        FStar_Syntax_Syntax.arg Prims.list ->
          FStar_Syntax_Syntax.arg Prims.list ctrl_tac
  =
  fun f  ->
    fun env  ->
      fun ctrl  ->
        fun ts  ->
          match ts with
          | [] -> ret ([], ctrl)
          | (t,q)::ts1 ->
              let uu____7429 = ctrl_tac_fold f env ctrl t  in
              bind uu____7429
                (fun uu____7457  ->
                   match uu____7457 with
                   | (t1,ctrl1) ->
                       let uu____7476 = ctrl_tac_fold_args f env ctrl1 ts1
                          in
                       bind uu____7476
                         (fun uu____7507  ->
                            match uu____7507 with
                            | (ts2,ctrl2) -> ret (((t1, q) :: ts2), ctrl2)))

let rewrite_rec :
  FStar_Tactics_Types.proofstate ->
    (FStar_Syntax_Syntax.term -> rewrite_result ctrl_tac) ->
      unit tac ->
        FStar_Options.optionstate ->
          FStar_TypeChecker_Env.env ->
            FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term ctrl_tac
  =
  fun ps  ->
    fun ctrl  ->
      fun rewriter  ->
        fun opts  ->
          fun env  ->
            fun t  ->
              let t1 = FStar_Syntax_Subst.compress t  in
              let uu____7603 =
                let uu____7610 =
                  add_irrelevant_goal "dummy" env FStar_Syntax_Util.t_true
                    opts
                   in
                bind uu____7610
                  (fun uu____7619  ->
                     let uu____7620 = ctrl t1  in
                     bind uu____7620
                       (fun res  ->
                          let uu____7643 = trivial ()  in
                          bind uu____7643 (fun uu____7651  -> ret res)))
                 in
              bind uu____7603
                (fun uu____7667  ->
                   match uu____7667 with
                   | (should_rewrite,ctrl1) ->
                       if Prims.op_Negation should_rewrite
                       then ret (t1, ctrl1)
                       else
                         (let uu____7691 =
                            FStar_TypeChecker_TcTerm.tc_term env t1  in
                          match uu____7691 with
                          | (t2,lcomp,g) ->
                              let uu____7707 =
                                (let uu____7710 =
                                   FStar_Syntax_Util.is_pure_or_ghost_lcomp
                                     lcomp
                                    in
                                 Prims.op_Negation uu____7710) ||
                                  (let uu____7712 =
                                     FStar_TypeChecker_Rel.is_trivial g  in
                                   Prims.op_Negation uu____7712)
                                 in
                              if uu____7707
                              then ret (t2, globalStop)
                              else
                                (let typ = lcomp.FStar_Syntax_Syntax.res_typ
                                    in
                                 let uu____7727 =
                                   new_uvar "pointwise_rec" env typ  in
                                 bind uu____7727
                                   (fun ut  ->
                                      log ps
                                        (fun uu____7742  ->
                                           let uu____7743 =
                                             FStar_Syntax_Print.term_to_string
                                               t2
                                              in
                                           let uu____7744 =
                                             FStar_Syntax_Print.term_to_string
                                               ut
                                              in
                                           FStar_Util.print2
                                             "Pointwise_rec: making equality\n\t%s ==\n\t%s\n"
                                             uu____7743 uu____7744);
                                      (let uu____7745 =
                                         let uu____7748 =
                                           let uu____7749 =
                                             FStar_TypeChecker_TcTerm.universe_of
                                               env typ
                                              in
                                           FStar_Syntax_Util.mk_eq2
                                             uu____7749 typ t2 ut
                                            in
                                         add_irrelevant_goal
                                           "rewrite_rec equation" env
                                           uu____7748 opts
                                          in
                                       bind uu____7745
                                         (fun uu____7756  ->
                                            let uu____7757 =
                                              bind rewriter
                                                (fun uu____7771  ->
                                                   let ut1 =
                                                     FStar_TypeChecker_Normalize.reduce_uvar_solutions
                                                       env ut
                                                      in
                                                   log ps
                                                     (fun uu____7777  ->
                                                        let uu____7778 =
                                                          FStar_Syntax_Print.term_to_string
                                                            t2
                                                           in
                                                        let uu____7779 =
                                                          FStar_Syntax_Print.term_to_string
                                                            ut1
                                                           in
                                                        FStar_Util.print2
                                                          "rewrite_rec: succeeded rewriting\n\t%s to\n\t%s\n"
                                                          uu____7778
                                                          uu____7779);
                                                   ret (ut1, ctrl1))
                                               in
                                            focus uu____7757))))))
  
let topdown_rewrite :
  (FStar_Syntax_Syntax.term ->
     (Prims.bool,FStar_BigInt.t) FStar_Pervasives_Native.tuple2 tac)
    -> unit tac -> unit tac
  =
  fun ctrl  ->
    fun rewriter  ->
      bind get
        (fun ps  ->
           let uu____7827 =
             match ps.FStar_Tactics_Types.goals with
             | g::gs -> (g, gs)
             | [] -> failwith "Pointwise: no goals"  in
           match uu____7827 with
           | (g,gs) ->
               let gt1 = g.FStar_Tactics_Types.goal_ty  in
               (log ps
                  (fun uu____7864  ->
                     let uu____7865 = FStar_Syntax_Print.term_to_string gt1
                        in
                     FStar_Util.print1 "Topdown_rewrite starting with %s\n"
                       uu____7865);
                bind dismiss_all
                  (fun uu____7868  ->
                     let uu____7869 =
                       ctrl_tac_fold
                         (rewrite_rec ps ctrl rewriter
                            g.FStar_Tactics_Types.opts)
                         g.FStar_Tactics_Types.context keepGoing gt1
                        in
                     bind uu____7869
                       (fun uu____7887  ->
                          match uu____7887 with
                          | (gt',uu____7895) ->
                              (log ps
                                 (fun uu____7899  ->
                                    let uu____7900 =
                                      FStar_Syntax_Print.term_to_string gt'
                                       in
                                    FStar_Util.print1
                                      "Topdown_rewrite seems to have succeded with %s\n"
                                      uu____7900);
                               (let uu____7901 = push_goals gs  in
                                bind uu____7901
                                  (fun uu____7905  ->
                                     add_goals
                                       [(let uu___120_7907 = g  in
                                         {
                                           FStar_Tactics_Types.context =
                                             (uu___120_7907.FStar_Tactics_Types.context);
                                           FStar_Tactics_Types.witness =
                                             (uu___120_7907.FStar_Tactics_Types.witness);
                                           FStar_Tactics_Types.goal_ty = gt';
                                           FStar_Tactics_Types.opts =
                                             (uu___120_7907.FStar_Tactics_Types.opts);
                                           FStar_Tactics_Types.is_guard =
                                             (uu___120_7907.FStar_Tactics_Types.is_guard)
                                         })])))))))
  
let pointwise : FStar_Tactics_Types.direction -> unit tac -> unit tac =
  fun d  ->
    fun tau  ->
      bind get
        (fun ps  ->
           let uu____7933 =
             match ps.FStar_Tactics_Types.goals with
             | g::gs -> (g, gs)
             | [] -> failwith "Pointwise: no goals"  in
           match uu____7933 with
           | (g,gs) ->
               let gt1 = g.FStar_Tactics_Types.goal_ty  in
               (log ps
                  (fun uu____7970  ->
                     let uu____7971 = FStar_Syntax_Print.term_to_string gt1
                        in
                     FStar_Util.print1 "Pointwise starting with %s\n"
                       uu____7971);
                bind dismiss_all
                  (fun uu____7974  ->
                     let uu____7975 =
                       tac_fold_env d
                         (pointwise_rec ps tau g.FStar_Tactics_Types.opts)
                         g.FStar_Tactics_Types.context gt1
                        in
                     bind uu____7975
                       (fun gt'  ->
                          log ps
                            (fun uu____7985  ->
                               let uu____7986 =
                                 FStar_Syntax_Print.term_to_string gt'  in
                               FStar_Util.print1
                                 "Pointwise seems to have succeded with %s\n"
                                 uu____7986);
                          (let uu____7987 = push_goals gs  in
                           bind uu____7987
                             (fun uu____7991  ->
                                add_goals
                                  [(let uu___121_7993 = g  in
                                    {
                                      FStar_Tactics_Types.context =
                                        (uu___121_7993.FStar_Tactics_Types.context);
                                      FStar_Tactics_Types.witness =
                                        (uu___121_7993.FStar_Tactics_Types.witness);
                                      FStar_Tactics_Types.goal_ty = gt';
                                      FStar_Tactics_Types.opts =
                                        (uu___121_7993.FStar_Tactics_Types.opts);
                                      FStar_Tactics_Types.is_guard =
                                        (uu___121_7993.FStar_Tactics_Types.is_guard)
                                    })]))))))
  
let trefl : unit -> unit tac =
  fun uu____8000  ->
    let uu____8003 = cur_goal ()  in
    bind uu____8003
      (fun g  ->
         let uu____8021 =
           FStar_Syntax_Util.un_squash g.FStar_Tactics_Types.goal_ty  in
         match uu____8021 with
         | FStar_Pervasives_Native.Some t ->
             let uu____8033 = FStar_Syntax_Util.head_and_args' t  in
             (match uu____8033 with
              | (hd1,args) ->
                  let uu____8066 =
                    let uu____8079 =
                      let uu____8080 = FStar_Syntax_Util.un_uinst hd1  in
                      uu____8080.FStar_Syntax_Syntax.n  in
                    (uu____8079, args)  in
                  (match uu____8066 with
                   | (FStar_Syntax_Syntax.Tm_fvar
                      fv,uu____8094::(l,uu____8096)::(r,uu____8098)::[]) when
                       FStar_Syntax_Syntax.fv_eq_lid fv
                         FStar_Parser_Const.eq2_lid
                       ->
                       let uu____8145 =
                         do_unify g.FStar_Tactics_Types.context l r  in
                       bind uu____8145
                         (fun b  ->
                            if Prims.op_Negation b
                            then
                              let uu____8154 =
                                tts g.FStar_Tactics_Types.context l  in
                              let uu____8155 =
                                tts g.FStar_Tactics_Types.context r  in
                              fail2
                                "trefl: not a trivial equality (%s vs %s)"
                                uu____8154 uu____8155
                            else solve g FStar_Syntax_Util.exp_unit)
                   | (hd2,uu____8158) ->
                       let uu____8175 = tts g.FStar_Tactics_Types.context t
                          in
                       fail1 "trefl: not an equality (%s)" uu____8175))
         | FStar_Pervasives_Native.None  -> fail "not an irrelevant goal")
  
let dup : unit -> unit tac =
  fun uu____8184  ->
    let uu____8187 = cur_goal ()  in
    bind uu____8187
      (fun g  ->
         let uu____8193 =
           new_uvar "dup" g.FStar_Tactics_Types.context
             g.FStar_Tactics_Types.goal_ty
            in
         bind uu____8193
           (fun u  ->
              let g' =
                let uu___122_8200 = g  in
                {
                  FStar_Tactics_Types.context =
                    (uu___122_8200.FStar_Tactics_Types.context);
                  FStar_Tactics_Types.witness = u;
                  FStar_Tactics_Types.goal_ty =
                    (uu___122_8200.FStar_Tactics_Types.goal_ty);
                  FStar_Tactics_Types.opts =
                    (uu___122_8200.FStar_Tactics_Types.opts);
                  FStar_Tactics_Types.is_guard =
                    (uu___122_8200.FStar_Tactics_Types.is_guard)
                }  in
              bind __dismiss
                (fun uu____8203  ->
                   let uu____8204 =
                     let uu____8207 =
                       let uu____8208 =
                         FStar_TypeChecker_TcTerm.universe_of
                           g.FStar_Tactics_Types.context
                           g.FStar_Tactics_Types.goal_ty
                          in
                       FStar_Syntax_Util.mk_eq2 uu____8208
                         g.FStar_Tactics_Types.goal_ty u
                         g.FStar_Tactics_Types.witness
                        in
                     add_irrelevant_goal "dup equation"
                       g.FStar_Tactics_Types.context uu____8207
                       g.FStar_Tactics_Types.opts
                      in
                   bind uu____8204
                     (fun uu____8211  ->
                        let uu____8212 = add_goals [g']  in
                        bind uu____8212 (fun uu____8216  -> ret ())))))
  
let flip : unit -> unit tac =
  fun uu____8223  ->
    bind get
      (fun ps  ->
         match ps.FStar_Tactics_Types.goals with
         | g1::g2::gs ->
             set
               (let uu___123_8240 = ps  in
                {
                  FStar_Tactics_Types.main_context =
                    (uu___123_8240.FStar_Tactics_Types.main_context);
                  FStar_Tactics_Types.main_goal =
                    (uu___123_8240.FStar_Tactics_Types.main_goal);
                  FStar_Tactics_Types.all_implicits =
                    (uu___123_8240.FStar_Tactics_Types.all_implicits);
                  FStar_Tactics_Types.goals = (g2 :: g1 :: gs);
                  FStar_Tactics_Types.smt_goals =
                    (uu___123_8240.FStar_Tactics_Types.smt_goals);
                  FStar_Tactics_Types.depth =
                    (uu___123_8240.FStar_Tactics_Types.depth);
                  FStar_Tactics_Types.__dump =
                    (uu___123_8240.FStar_Tactics_Types.__dump);
                  FStar_Tactics_Types.psc =
                    (uu___123_8240.FStar_Tactics_Types.psc);
                  FStar_Tactics_Types.entry_range =
                    (uu___123_8240.FStar_Tactics_Types.entry_range);
                  FStar_Tactics_Types.guard_policy =
                    (uu___123_8240.FStar_Tactics_Types.guard_policy);
                  FStar_Tactics_Types.freshness =
                    (uu___123_8240.FStar_Tactics_Types.freshness)
                })
         | uu____8241 -> fail "flip: less than 2 goals")
  
let later : unit -> unit tac =
  fun uu____8250  ->
    bind get
      (fun ps  ->
         match ps.FStar_Tactics_Types.goals with
         | [] -> ret ()
         | g::gs ->
             set
               (let uu___124_8263 = ps  in
                {
                  FStar_Tactics_Types.main_context =
                    (uu___124_8263.FStar_Tactics_Types.main_context);
                  FStar_Tactics_Types.main_goal =
                    (uu___124_8263.FStar_Tactics_Types.main_goal);
                  FStar_Tactics_Types.all_implicits =
                    (uu___124_8263.FStar_Tactics_Types.all_implicits);
                  FStar_Tactics_Types.goals = (FStar_List.append gs [g]);
                  FStar_Tactics_Types.smt_goals =
                    (uu___124_8263.FStar_Tactics_Types.smt_goals);
                  FStar_Tactics_Types.depth =
                    (uu___124_8263.FStar_Tactics_Types.depth);
                  FStar_Tactics_Types.__dump =
                    (uu___124_8263.FStar_Tactics_Types.__dump);
                  FStar_Tactics_Types.psc =
                    (uu___124_8263.FStar_Tactics_Types.psc);
                  FStar_Tactics_Types.entry_range =
                    (uu___124_8263.FStar_Tactics_Types.entry_range);
                  FStar_Tactics_Types.guard_policy =
                    (uu___124_8263.FStar_Tactics_Types.guard_policy);
                  FStar_Tactics_Types.freshness =
                    (uu___124_8263.FStar_Tactics_Types.freshness)
                }))
  
let qed : unit -> unit tac =
  fun uu____8270  ->
    bind get
      (fun ps  ->
         match ps.FStar_Tactics_Types.goals with
         | [] -> ret ()
         | uu____8277 -> fail "Not done!")
  
let cases :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 tac
  =
  fun t  ->
    let uu____8297 =
      let uu____8304 = cur_goal ()  in
      bind uu____8304
        (fun g  ->
           let uu____8314 = __tc g.FStar_Tactics_Types.context t  in
           bind uu____8314
             (fun uu____8350  ->
                match uu____8350 with
                | (t1,typ,guard) ->
                    let uu____8366 = FStar_Syntax_Util.head_and_args typ  in
                    (match uu____8366 with
                     | (hd1,args) ->
                         let uu____8409 =
                           let uu____8422 =
                             let uu____8423 = FStar_Syntax_Util.un_uinst hd1
                                in
                             uu____8423.FStar_Syntax_Syntax.n  in
                           (uu____8422, args)  in
                         (match uu____8409 with
                          | (FStar_Syntax_Syntax.Tm_fvar
                             fv,(p,uu____8442)::(q,uu____8444)::[]) when
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
                                let uu___125_8482 = g  in
                                let uu____8483 =
                                  FStar_TypeChecker_Env.push_bv
                                    g.FStar_Tactics_Types.context v_p
                                   in
                                {
                                  FStar_Tactics_Types.context = uu____8483;
                                  FStar_Tactics_Types.witness =
                                    (uu___125_8482.FStar_Tactics_Types.witness);
                                  FStar_Tactics_Types.goal_ty =
                                    (uu___125_8482.FStar_Tactics_Types.goal_ty);
                                  FStar_Tactics_Types.opts =
                                    (uu___125_8482.FStar_Tactics_Types.opts);
                                  FStar_Tactics_Types.is_guard =
                                    (uu___125_8482.FStar_Tactics_Types.is_guard)
                                }  in
                              let g2 =
                                let uu___126_8485 = g  in
                                let uu____8486 =
                                  FStar_TypeChecker_Env.push_bv
                                    g.FStar_Tactics_Types.context v_q
                                   in
                                {
                                  FStar_Tactics_Types.context = uu____8486;
                                  FStar_Tactics_Types.witness =
                                    (uu___126_8485.FStar_Tactics_Types.witness);
                                  FStar_Tactics_Types.goal_ty =
                                    (uu___126_8485.FStar_Tactics_Types.goal_ty);
                                  FStar_Tactics_Types.opts =
                                    (uu___126_8485.FStar_Tactics_Types.opts);
                                  FStar_Tactics_Types.is_guard =
                                    (uu___126_8485.FStar_Tactics_Types.is_guard)
                                }  in
                              bind __dismiss
                                (fun uu____8493  ->
                                   let uu____8494 = add_goals [g1; g2]  in
                                   bind uu____8494
                                     (fun uu____8503  ->
                                        let uu____8504 =
                                          let uu____8509 =
                                            FStar_Syntax_Syntax.bv_to_name
                                              v_p
                                             in
                                          let uu____8510 =
                                            FStar_Syntax_Syntax.bv_to_name
                                              v_q
                                             in
                                          (uu____8509, uu____8510)  in
                                        ret uu____8504))
                          | uu____8515 ->
                              let uu____8528 =
                                tts g.FStar_Tactics_Types.context typ  in
                              fail1 "Not a disjunction: %s" uu____8528))))
       in
    FStar_All.pipe_left (wrap_err "cases") uu____8297
  
let set_options : Prims.string -> unit tac =
  fun s  ->
    let uu____8558 = cur_goal ()  in
    bind uu____8558
      (fun g  ->
         FStar_Options.push ();
         (let uu____8571 = FStar_Util.smap_copy g.FStar_Tactics_Types.opts
             in
          FStar_Options.set uu____8571);
         (let res = FStar_Options.set_options FStar_Options.Set s  in
          let opts' = FStar_Options.peek ()  in
          FStar_Options.pop ();
          (match res with
           | FStar_Getopt.Success  ->
               let g' =
                 let uu___127_8578 = g  in
                 {
                   FStar_Tactics_Types.context =
                     (uu___127_8578.FStar_Tactics_Types.context);
                   FStar_Tactics_Types.witness =
                     (uu___127_8578.FStar_Tactics_Types.witness);
                   FStar_Tactics_Types.goal_ty =
                     (uu___127_8578.FStar_Tactics_Types.goal_ty);
                   FStar_Tactics_Types.opts = opts';
                   FStar_Tactics_Types.is_guard =
                     (uu___127_8578.FStar_Tactics_Types.is_guard)
                 }  in
               replace_cur g'
           | FStar_Getopt.Error err ->
               fail2 "Setting options `%s` failed: %s" s err
           | FStar_Getopt.Help  ->
               fail1 "Setting options `%s` failed (got `Help`?)" s)))
  
let top_env : unit -> env tac =
  fun uu____8586  ->
    bind get
      (fun ps  -> FStar_All.pipe_left ret ps.FStar_Tactics_Types.main_context)
  
let cur_env : unit -> env tac =
  fun uu____8599  ->
    let uu____8602 = cur_goal ()  in
    bind uu____8602
      (fun g  -> FStar_All.pipe_left ret g.FStar_Tactics_Types.context)
  
let cur_goal' : unit -> FStar_Syntax_Syntax.term tac =
  fun uu____8615  ->
    let uu____8618 = cur_goal ()  in
    bind uu____8618
      (fun g  -> FStar_All.pipe_left ret g.FStar_Tactics_Types.goal_ty)
  
let cur_witness : unit -> FStar_Syntax_Syntax.term tac =
  fun uu____8631  ->
    let uu____8634 = cur_goal ()  in
    bind uu____8634
      (fun g  -> FStar_All.pipe_left ret g.FStar_Tactics_Types.witness)
  
let unquote :
  FStar_Reflection_Data.typ ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac
  =
  fun ty  ->
    fun tm  ->
      let uu____8655 =
        let uu____8658 = cur_goal ()  in
        bind uu____8658
          (fun goal  ->
             let env =
               FStar_TypeChecker_Env.set_expected_typ
                 goal.FStar_Tactics_Types.context ty
                in
             let uu____8666 = __tc env tm  in
             bind uu____8666
               (fun uu____8686  ->
                  match uu____8686 with
                  | (tm1,typ,guard) ->
                      let uu____8698 =
                        proc_guard "unquote" env guard
                          goal.FStar_Tactics_Types.opts
                         in
                      bind uu____8698 (fun uu____8702  -> ret tm1)))
         in
      FStar_All.pipe_left (wrap_err "unquote") uu____8655
  
let uvar_env :
  env ->
    FStar_Reflection_Data.typ FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.term tac
  =
  fun env  ->
    fun ty  ->
      let uu____8725 =
        match ty with
        | FStar_Pervasives_Native.Some ty1 -> ret ty1
        | FStar_Pervasives_Native.None  ->
            let uu____8731 =
              let uu____8732 = FStar_Syntax_Util.type_u ()  in
              FStar_All.pipe_left FStar_Pervasives_Native.fst uu____8732  in
            new_uvar "uvar_env.2" env uu____8731
         in
      bind uu____8725
        (fun typ  ->
           let uu____8744 = new_uvar "uvar_env" env typ  in
           bind uu____8744 (fun t  -> ret t))
  
let unshelve : FStar_Syntax_Syntax.term -> unit tac =
  fun t  ->
    let uu____8758 =
      bind get
        (fun ps  ->
           let env = ps.FStar_Tactics_Types.main_context  in
           let opts =
             match ps.FStar_Tactics_Types.goals with
             | g::uu____8775 -> g.FStar_Tactics_Types.opts
             | uu____8778 -> FStar_Options.peek ()  in
           let uu____8781 = FStar_Syntax_Util.head_and_args t  in
           match uu____8781 with
           | ({
                FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                  (uu____8798,typ);
                FStar_Syntax_Syntax.pos = uu____8800;
                FStar_Syntax_Syntax.vars = uu____8801;_},uu____8802)
               ->
               let uu____8847 =
                 let uu____8850 =
                   let uu____8851 = bnorm env t  in
                   let uu____8852 = bnorm env typ  in
                   {
                     FStar_Tactics_Types.context = env;
                     FStar_Tactics_Types.witness = uu____8851;
                     FStar_Tactics_Types.goal_ty = uu____8852;
                     FStar_Tactics_Types.opts = opts;
                     FStar_Tactics_Types.is_guard = false
                   }  in
                 [uu____8850]  in
               add_goals uu____8847
           | uu____8853 -> fail "not a uvar")
       in
    FStar_All.pipe_left (wrap_err "unshelve") uu____8758
  
let unify :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool tac =
  fun t1  ->
    fun t2  ->
      bind get
        (fun ps  -> do_unify ps.FStar_Tactics_Types.main_context t1 t2)
  
let launch_process :
  Prims.string -> Prims.string -> Prims.string -> Prims.string tac =
  fun prog  ->
    fun args  ->
      fun input  ->
        bind idtac
          (fun uu____8910  ->
             let uu____8911 = FStar_Options.unsafe_tactic_exec ()  in
             if uu____8911
             then
               let s =
                 FStar_Util.launch_process true "tactic_launch" prog args
                   input (fun uu____8917  -> fun uu____8918  -> false)
                  in
               ret s
             else
               fail
                 "launch_process: will not run anything unless --unsafe_tactic_exec is provided")
  
let fresh_bv_named :
  Prims.string -> FStar_Reflection_Data.typ -> FStar_Syntax_Syntax.bv tac =
  fun nm  ->
    fun t  ->
      bind idtac
        (fun uu____8936  ->
           let uu____8937 =
             FStar_Syntax_Syntax.gen_bv nm FStar_Pervasives_Native.None t  in
           ret uu____8937)
  
let change : FStar_Reflection_Data.typ -> unit tac =
  fun ty  ->
    let uu____8947 =
      mlog
        (fun uu____8952  ->
           let uu____8953 = FStar_Syntax_Print.term_to_string ty  in
           FStar_Util.print1 "change: ty = %s\n" uu____8953)
        (fun uu____8956  ->
           let uu____8957 = cur_goal ()  in
           bind uu____8957
             (fun g  ->
                let uu____8963 = __tc g.FStar_Tactics_Types.context ty  in
                bind uu____8963
                  (fun uu____8983  ->
                     match uu____8983 with
                     | (ty1,uu____8993,guard) ->
                         let uu____8995 =
                           proc_guard "change" g.FStar_Tactics_Types.context
                             guard g.FStar_Tactics_Types.opts
                            in
                         bind uu____8995
                           (fun uu____9000  ->
                              let uu____9001 =
                                do_unify g.FStar_Tactics_Types.context
                                  g.FStar_Tactics_Types.goal_ty ty1
                                 in
                              bind uu____9001
                                (fun bb  ->
                                   if bb
                                   then
                                     replace_cur
                                       (let uu___128_9010 = g  in
                                        {
                                          FStar_Tactics_Types.context =
                                            (uu___128_9010.FStar_Tactics_Types.context);
                                          FStar_Tactics_Types.witness =
                                            (uu___128_9010.FStar_Tactics_Types.witness);
                                          FStar_Tactics_Types.goal_ty = ty1;
                                          FStar_Tactics_Types.opts =
                                            (uu___128_9010.FStar_Tactics_Types.opts);
                                          FStar_Tactics_Types.is_guard =
                                            (uu___128_9010.FStar_Tactics_Types.is_guard)
                                        })
                                   else
                                     (let steps =
                                        [FStar_TypeChecker_Normalize.Reify;
                                        FStar_TypeChecker_Normalize.UnfoldUntil
                                          FStar_Syntax_Syntax.Delta_constant;
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
                                      let uu____9017 =
                                        do_unify
                                          g.FStar_Tactics_Types.context ng
                                          nty
                                         in
                                      bind uu____9017
                                        (fun b  ->
                                           if b
                                           then
                                             replace_cur
                                               (let uu___129_9026 = g  in
                                                {
                                                  FStar_Tactics_Types.context
                                                    =
                                                    (uu___129_9026.FStar_Tactics_Types.context);
                                                  FStar_Tactics_Types.witness
                                                    =
                                                    (uu___129_9026.FStar_Tactics_Types.witness);
                                                  FStar_Tactics_Types.goal_ty
                                                    = ty1;
                                                  FStar_Tactics_Types.opts =
                                                    (uu___129_9026.FStar_Tactics_Types.opts);
                                                  FStar_Tactics_Types.is_guard
                                                    =
                                                    (uu___129_9026.FStar_Tactics_Types.is_guard)
                                                })
                                           else fail "not convertible")))))))
       in
    FStar_All.pipe_left (wrap_err "change") uu____8947
  
let rec last : 'a . 'a Prims.list -> 'a =
  fun l  ->
    match l with
    | [] -> failwith "last: empty list"
    | x::[] -> x
    | uu____9048::xs -> last xs
  
let rec init : 'a . 'a Prims.list -> 'a Prims.list =
  fun l  ->
    match l with
    | [] -> failwith "init: empty list"
    | x::[] -> []
    | x::xs -> let uu____9076 = init xs  in x :: uu____9076
  
let rec inspect :
  FStar_Syntax_Syntax.term -> FStar_Reflection_Data.term_view tac =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t  in
    let t2 = FStar_Syntax_Util.un_uinst t1  in
    match t2.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_meta (t3,uu____9093) -> inspect t3
    | FStar_Syntax_Syntax.Tm_name bv ->
        FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_Var bv)
    | FStar_Syntax_Syntax.Tm_bvar bv ->
        FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_BVar bv)
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_FVar fv)
    | FStar_Syntax_Syntax.Tm_app (hd1,[]) ->
        failwith "inspect: empty arguments on Tm_app"
    | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
        let uu____9150 = last args  in
        (match uu____9150 with
         | (a,q) ->
             let q' = FStar_Reflection_Basic.inspect_aqual q  in
             let uu____9172 =
               let uu____9173 =
                 let uu____9178 =
                   let uu____9181 =
                     let uu____9186 = init args  in
                     FStar_Syntax_Syntax.mk_Tm_app hd1 uu____9186  in
                   uu____9181 FStar_Pervasives_Native.None
                     t2.FStar_Syntax_Syntax.pos
                    in
                 (uu____9178, (a, q'))  in
               FStar_Reflection_Data.Tv_App uu____9173  in
             FStar_All.pipe_left ret uu____9172)
    | FStar_Syntax_Syntax.Tm_abs ([],uu____9207,uu____9208) ->
        failwith "inspect: empty arguments on Tm_abs"
    | FStar_Syntax_Syntax.Tm_abs (bs,t3,k) ->
        let uu____9252 = FStar_Syntax_Subst.open_term bs t3  in
        (match uu____9252 with
         | (bs1,t4) ->
             (match bs1 with
              | [] -> failwith "impossible"
              | b::bs2 ->
                  let uu____9285 =
                    let uu____9286 =
                      let uu____9291 = FStar_Syntax_Util.abs bs2 t4 k  in
                      (b, uu____9291)  in
                    FStar_Reflection_Data.Tv_Abs uu____9286  in
                  FStar_All.pipe_left ret uu____9285))
    | FStar_Syntax_Syntax.Tm_type uu____9298 ->
        FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_Type ())
    | FStar_Syntax_Syntax.Tm_arrow ([],k) ->
        failwith "inspect: empty binders on arrow"
    | FStar_Syntax_Syntax.Tm_arrow uu____9318 ->
        let uu____9331 = FStar_Syntax_Util.arrow_one t2  in
        (match uu____9331 with
         | FStar_Pervasives_Native.Some (b,c) ->
             FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_Arrow (b, c))
         | FStar_Pervasives_Native.None  -> failwith "impossible")
    | FStar_Syntax_Syntax.Tm_refine (bv,t3) ->
        let b = FStar_Syntax_Syntax.mk_binder bv  in
        let uu____9361 = FStar_Syntax_Subst.open_term [b] t3  in
        (match uu____9361 with
         | (b',t4) ->
             let b1 =
               match b' with
               | b'1::[] -> b'1
               | uu____9392 -> failwith "impossible"  in
             FStar_All.pipe_left ret
               (FStar_Reflection_Data.Tv_Refine
                  ((FStar_Pervasives_Native.fst b1), t4)))
    | FStar_Syntax_Syntax.Tm_constant c ->
        let uu____9400 =
          let uu____9401 = FStar_Reflection_Basic.inspect_const c  in
          FStar_Reflection_Data.Tv_Const uu____9401  in
        FStar_All.pipe_left ret uu____9400
    | FStar_Syntax_Syntax.Tm_uvar (u,t3) ->
        let uu____9430 =
          let uu____9431 =
            let uu____9436 =
              let uu____9437 = FStar_Syntax_Unionfind.uvar_id u  in
              FStar_BigInt.of_int_fs uu____9437  in
            (uu____9436, t3)  in
          FStar_Reflection_Data.Tv_Uvar uu____9431  in
        FStar_All.pipe_left ret uu____9430
    | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),t21) ->
        if lb.FStar_Syntax_Syntax.lbunivs <> []
        then FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
        else
          (match lb.FStar_Syntax_Syntax.lbname with
           | FStar_Util.Inr uu____9465 ->
               FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
           | FStar_Util.Inl bv ->
               let b = FStar_Syntax_Syntax.mk_binder bv  in
               let uu____9470 = FStar_Syntax_Subst.open_term [b] t21  in
               (match uu____9470 with
                | (bs,t22) ->
                    let b1 =
                      match bs with
                      | b1::[] -> b1
                      | uu____9501 ->
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
           | FStar_Util.Inr uu____9533 ->
               FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
           | FStar_Util.Inl bv ->
               let uu____9537 = FStar_Syntax_Subst.open_let_rec [lb] t21  in
               (match uu____9537 with
                | (lbs,t22) ->
                    (match lbs with
                     | lb1::[] ->
                         (match lb1.FStar_Syntax_Syntax.lbname with
                          | FStar_Util.Inr uu____9557 ->
                              ret FStar_Reflection_Data.Tv_Unknown
                          | FStar_Util.Inl bv1 ->
                              FStar_All.pipe_left ret
                                (FStar_Reflection_Data.Tv_Let
                                   (true, bv1,
                                     (lb1.FStar_Syntax_Syntax.lbdef), t22)))
                     | uu____9563 ->
                         failwith
                           "impossible: open_term returned different amount of binders")))
    | FStar_Syntax_Syntax.Tm_match (t3,brs) ->
        let rec inspect_pat p =
          match p.FStar_Syntax_Syntax.v with
          | FStar_Syntax_Syntax.Pat_constant c ->
              let uu____9617 = FStar_Reflection_Basic.inspect_const c  in
              FStar_Reflection_Data.Pat_Constant uu____9617
          | FStar_Syntax_Syntax.Pat_cons (fv,ps) ->
              let uu____9636 =
                let uu____9643 =
                  FStar_List.map
                    (fun uu____9655  ->
                       match uu____9655 with
                       | (p1,uu____9663) -> inspect_pat p1) ps
                   in
                (fv, uu____9643)  in
              FStar_Reflection_Data.Pat_Cons uu____9636
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
            (fun uu___63_9717  ->
               match uu___63_9717 with
               | (pat,uu____9739,t4) ->
                   let uu____9757 = inspect_pat pat  in (uu____9757, t4))
            brs1
           in
        FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_Match (t3, brs2))
    | FStar_Syntax_Syntax.Tm_unknown  ->
        FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
    | uu____9774 ->
        ((let uu____9776 =
            let uu____9781 =
              let uu____9782 = FStar_Syntax_Print.tag_of_term t2  in
              let uu____9783 = FStar_Syntax_Print.term_to_string t2  in
              FStar_Util.format2
                "inspect: outside of expected syntax (%s, %s)\n" uu____9782
                uu____9783
               in
            (FStar_Errors.Warning_CantInspect, uu____9781)  in
          FStar_Errors.log_issue t2.FStar_Syntax_Syntax.pos uu____9776);
         FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown)
  
let pack : FStar_Reflection_Data.term_view -> FStar_Syntax_Syntax.term tac =
  fun tv  ->
    match tv with
    | FStar_Reflection_Data.Tv_Var bv ->
        let uu____9796 = FStar_Syntax_Syntax.bv_to_name bv  in
        FStar_All.pipe_left ret uu____9796
    | FStar_Reflection_Data.Tv_BVar bv ->
        let uu____9800 = FStar_Syntax_Syntax.bv_to_tm bv  in
        FStar_All.pipe_left ret uu____9800
    | FStar_Reflection_Data.Tv_FVar fv ->
        let uu____9804 = FStar_Syntax_Syntax.fv_to_tm fv  in
        FStar_All.pipe_left ret uu____9804
    | FStar_Reflection_Data.Tv_App (l,(r,q)) ->
        let q' = FStar_Reflection_Basic.pack_aqual q  in
        let uu____9815 = FStar_Syntax_Util.mk_app l [(r, q')]  in
        FStar_All.pipe_left ret uu____9815
    | FStar_Reflection_Data.Tv_Abs (b,t) ->
        let uu____9836 =
          FStar_Syntax_Util.abs [b] t FStar_Pervasives_Native.None  in
        FStar_All.pipe_left ret uu____9836
    | FStar_Reflection_Data.Tv_Arrow (b,c) ->
        let uu____9841 = FStar_Syntax_Util.arrow [b] c  in
        FStar_All.pipe_left ret uu____9841
    | FStar_Reflection_Data.Tv_Type () ->
        FStar_All.pipe_left ret FStar_Syntax_Util.ktype
    | FStar_Reflection_Data.Tv_Refine (bv,t) ->
        let uu____9862 = FStar_Syntax_Util.refine bv t  in
        FStar_All.pipe_left ret uu____9862
    | FStar_Reflection_Data.Tv_Const c ->
        let uu____9874 =
          let uu____9877 =
            let uu____9884 =
              let uu____9885 = FStar_Reflection_Basic.pack_const c  in
              FStar_Syntax_Syntax.Tm_constant uu____9885  in
            FStar_Syntax_Syntax.mk uu____9884  in
          uu____9877 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
        FStar_All.pipe_left ret uu____9874
    | FStar_Reflection_Data.Tv_Uvar (u,t) ->
        let uu____9899 =
          let uu____9902 = FStar_BigInt.to_int_fs u  in
          FStar_Syntax_Util.uvar_from_id uu____9902 t  in
        FStar_All.pipe_left ret uu____9899
    | FStar_Reflection_Data.Tv_Let (false ,bv,t1,t2) ->
        let lb =
          FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl bv) []
            bv.FStar_Syntax_Syntax.sort FStar_Parser_Const.effect_Tot_lid t1
            [] FStar_Range.dummyRange
           in
        let uu____9917 =
          let uu____9920 =
            let uu____9927 =
              let uu____9928 =
                let uu____9941 =
                  let uu____9942 =
                    let uu____9943 = FStar_Syntax_Syntax.mk_binder bv  in
                    [uu____9943]  in
                  FStar_Syntax_Subst.close uu____9942 t2  in
                ((false, [lb]), uu____9941)  in
              FStar_Syntax_Syntax.Tm_let uu____9928  in
            FStar_Syntax_Syntax.mk uu____9927  in
          uu____9920 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
        FStar_All.pipe_left ret uu____9917
    | FStar_Reflection_Data.Tv_Let (true ,bv,t1,t2) ->
        let lb =
          FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl bv) []
            bv.FStar_Syntax_Syntax.sort FStar_Parser_Const.effect_Tot_lid t1
            [] FStar_Range.dummyRange
           in
        let uu____9969 = FStar_Syntax_Subst.close_let_rec [lb] t2  in
        (match uu____9969 with
         | (lbs,body) ->
             let uu____9984 =
               FStar_Syntax_Syntax.mk
                 (FStar_Syntax_Syntax.Tm_let ((true, lbs), body))
                 FStar_Pervasives_Native.None FStar_Range.dummyRange
                in
             FStar_All.pipe_left ret uu____9984)
    | FStar_Reflection_Data.Tv_Match (t,brs) ->
        let wrap v1 =
          {
            FStar_Syntax_Syntax.v = v1;
            FStar_Syntax_Syntax.p = FStar_Range.dummyRange
          }  in
        let rec pack_pat p =
          match p with
          | FStar_Reflection_Data.Pat_Constant c ->
              let uu____10024 =
                let uu____10025 = FStar_Reflection_Basic.pack_const c  in
                FStar_Syntax_Syntax.Pat_constant uu____10025  in
              FStar_All.pipe_left wrap uu____10024
          | FStar_Reflection_Data.Pat_Cons (fv,ps) ->
              let uu____10034 =
                let uu____10035 =
                  let uu____10048 =
                    FStar_List.map
                      (fun p1  ->
                         let uu____10062 = pack_pat p1  in
                         (uu____10062, false)) ps
                     in
                  (fv, uu____10048)  in
                FStar_Syntax_Syntax.Pat_cons uu____10035  in
              FStar_All.pipe_left wrap uu____10034
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
            (fun uu___64_10112  ->
               match uu___64_10112 with
               | (pat,t1) ->
                   let uu____10129 = pack_pat pat  in
                   (uu____10129, FStar_Pervasives_Native.None, t1)) brs
           in
        let brs2 = FStar_List.map FStar_Syntax_Subst.close_branch brs1  in
        let uu____10139 =
          FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_match (t, brs2))
            FStar_Pervasives_Native.None FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____10139
    | FStar_Reflection_Data.Tv_AscribedT (e,t,tacopt) ->
        let uu____10159 =
          FStar_Syntax_Syntax.mk
            (FStar_Syntax_Syntax.Tm_ascribed
               (e, ((FStar_Util.Inl t), tacopt),
                 FStar_Pervasives_Native.None)) FStar_Pervasives_Native.None
            FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____10159
    | FStar_Reflection_Data.Tv_AscribedC (e,c,tacopt) ->
        let uu____10201 =
          FStar_Syntax_Syntax.mk
            (FStar_Syntax_Syntax.Tm_ascribed
               (e, ((FStar_Util.Inr c), tacopt),
                 FStar_Pervasives_Native.None)) FStar_Pervasives_Native.None
            FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____10201
    | FStar_Reflection_Data.Tv_Unknown  ->
        let uu____10236 =
          FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
            FStar_Pervasives_Native.None FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____10236
  
let goal_of_goal_ty :
  env ->
    FStar_Reflection_Data.typ ->
      (FStar_Tactics_Types.goal,FStar_TypeChecker_Env.guard_t)
        FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun typ  ->
      let uu____10265 =
        FStar_TypeChecker_Util.new_implicit_var "proofstate_of_goal_ty"
          typ.FStar_Syntax_Syntax.pos env typ
         in
      match uu____10265 with
      | (u,uu____10283,g_u) ->
          let g =
            let uu____10298 = FStar_Options.peek ()  in
            {
              FStar_Tactics_Types.context = env;
              FStar_Tactics_Types.witness = u;
              FStar_Tactics_Types.goal_ty = typ;
              FStar_Tactics_Types.opts = uu____10298;
              FStar_Tactics_Types.is_guard = false
            }  in
          (g, g_u)
  
let proofstate_of_goal_ty :
  env ->
    FStar_Reflection_Data.typ ->
      (FStar_Tactics_Types.proofstate,FStar_Syntax_Syntax.term)
        FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun typ  ->
      let uu____10313 = goal_of_goal_ty env typ  in
      match uu____10313 with
      | (g,g_u) ->
          let ps =
            {
              FStar_Tactics_Types.main_context = env;
              FStar_Tactics_Types.main_goal = g;
              FStar_Tactics_Types.all_implicits =
                (g_u.FStar_TypeChecker_Env.implicits);
              FStar_Tactics_Types.goals = [g];
              FStar_Tactics_Types.smt_goals = [];
              FStar_Tactics_Types.depth = (Prims.lift_native_int (0));
              FStar_Tactics_Types.__dump =
                (fun ps  -> fun msg  -> dump_proofstate ps msg);
              FStar_Tactics_Types.psc = FStar_TypeChecker_Normalize.null_psc;
              FStar_Tactics_Types.entry_range = FStar_Range.dummyRange;
              FStar_Tactics_Types.guard_policy = FStar_Tactics_Types.SMT;
              FStar_Tactics_Types.freshness = (Prims.lift_native_int (0))
            }  in
          (ps, (g.FStar_Tactics_Types.witness))
  