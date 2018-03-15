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
           let uu____140 = run t1 p  in
           match uu____140 with
           | FStar_Tactics_Result.Success (a,q) ->
               let uu____147 = t2 a  in run uu____147 q
           | FStar_Tactics_Result.Failed (msg,q) ->
               FStar_Tactics_Result.Failed (msg, q))
  
let (idtac : Prims.unit tac) = ret () 
let (goal_to_string : FStar_Tactics_Types.goal -> Prims.string) =
  fun g  ->
    let g_binders =
      let uu____158 =
        FStar_TypeChecker_Env.all_binders g.FStar_Tactics_Types.context  in
      FStar_All.pipe_right uu____158
        (FStar_Syntax_Print.binders_to_string ", ")
       in
    let w = bnorm g.FStar_Tactics_Types.context g.FStar_Tactics_Types.witness
       in
    let t = bnorm g.FStar_Tactics_Types.context g.FStar_Tactics_Types.goal_ty
       in
    let uu____161 = tts g.FStar_Tactics_Types.context w  in
    let uu____162 = tts g.FStar_Tactics_Types.context t  in
    FStar_Util.format3 "%s |- %s : %s" g_binders uu____161 uu____162
  
let (tacprint : Prims.string -> Prims.unit) =
  fun s  -> FStar_Util.print1 "TAC>> %s\n" s 
let (tacprint1 : Prims.string -> Prims.string -> Prims.unit) =
  fun s  ->
    fun x  ->
      let uu____172 = FStar_Util.format1 s x  in
      FStar_Util.print1 "TAC>> %s\n" uu____172
  
let (tacprint2 : Prims.string -> Prims.string -> Prims.string -> Prims.unit)
  =
  fun s  ->
    fun x  ->
      fun y  ->
        let uu____182 = FStar_Util.format2 s x y  in
        FStar_Util.print1 "TAC>> %s\n" uu____182
  
let (tacprint3 :
  Prims.string -> Prims.string -> Prims.string -> Prims.string -> Prims.unit)
  =
  fun s  ->
    fun x  ->
      fun y  ->
        fun z  ->
          let uu____195 = FStar_Util.format3 s x y z  in
          FStar_Util.print1 "TAC>> %s\n" uu____195
  
let (comp_to_typ : FStar_Syntax_Syntax.comp -> FStar_Reflection_Data.typ) =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total (t,uu____200) -> t
    | FStar_Syntax_Syntax.GTotal (t,uu____210) -> t
    | FStar_Syntax_Syntax.Comp ct -> ct.FStar_Syntax_Syntax.result_typ
  
let (is_irrelevant : FStar_Tactics_Types.goal -> Prims.bool) =
  fun g  ->
    let uu____223 =
      let uu____228 =
        FStar_TypeChecker_Normalize.unfold_whnf g.FStar_Tactics_Types.context
          g.FStar_Tactics_Types.goal_ty
         in
      FStar_Syntax_Util.un_squash uu____228  in
    match uu____223 with
    | FStar_Pervasives_Native.Some t -> true
    | uu____234 -> false
  
let dump_goal :
  'Auu____242 . 'Auu____242 -> FStar_Tactics_Types.goal -> Prims.unit =
  fun ps  ->
    fun goal  -> let uu____252 = goal_to_string goal  in tacprint uu____252
  
let (dump_cur : FStar_Tactics_Types.proofstate -> Prims.string -> Prims.unit)
  =
  fun ps  ->
    fun msg  ->
      match ps.FStar_Tactics_Types.goals with
      | [] -> tacprint1 "No more goals (%s)" msg
      | h::uu____260 ->
          (tacprint1 "Current goal (%s):" msg;
           (let uu____264 = FStar_List.hd ps.FStar_Tactics_Types.goals  in
            dump_goal ps uu____264))
  
let (ps_to_string :
  (Prims.string,FStar_Tactics_Types.proofstate)
    FStar_Pervasives_Native.tuple2 -> Prims.string)
  =
  fun uu____271  ->
    match uu____271 with
    | (msg,ps) ->
        let uu____278 =
          let uu____281 =
            let uu____282 =
              FStar_Util.string_of_int ps.FStar_Tactics_Types.depth  in
            FStar_Util.format2 "State dump @ depth %s (%s):\n" uu____282 msg
             in
          let uu____283 =
            let uu____286 =
              let uu____287 =
                FStar_Range.string_of_range
                  ps.FStar_Tactics_Types.entry_range
                 in
              FStar_Util.format1 "Location: %s\n" uu____287  in
            let uu____288 =
              let uu____291 =
                let uu____292 =
                  FStar_Util.string_of_int
                    (FStar_List.length ps.FStar_Tactics_Types.goals)
                   in
                let uu____293 =
                  let uu____294 =
                    FStar_List.map goal_to_string
                      ps.FStar_Tactics_Types.goals
                     in
                  FStar_String.concat "\n" uu____294  in
                FStar_Util.format2 "ACTIVE goals (%s):\n%s\n" uu____292
                  uu____293
                 in
              let uu____297 =
                let uu____300 =
                  let uu____301 =
                    FStar_Util.string_of_int
                      (FStar_List.length ps.FStar_Tactics_Types.smt_goals)
                     in
                  let uu____302 =
                    let uu____303 =
                      FStar_List.map goal_to_string
                        ps.FStar_Tactics_Types.smt_goals
                       in
                    FStar_String.concat "\n" uu____303  in
                  FStar_Util.format2 "SMT goals (%s):\n%s\n" uu____301
                    uu____302
                   in
                [uu____300]  in
              uu____291 :: uu____297  in
            uu____286 :: uu____288  in
          uu____281 :: uu____283  in
        FStar_String.concat "" uu____278
  
let (goal_to_json : FStar_Tactics_Types.goal -> FStar_Util.json) =
  fun g  ->
    let g_binders =
      let uu____310 =
        FStar_TypeChecker_Env.all_binders g.FStar_Tactics_Types.context  in
      let uu____311 =
        let uu____314 =
          FStar_TypeChecker_Env.dsenv g.FStar_Tactics_Types.context  in
        FStar_Syntax_Print.binders_to_json uu____314  in
      FStar_All.pipe_right uu____310 uu____311  in
    let uu____315 =
      let uu____322 =
        let uu____329 =
          let uu____334 =
            let uu____335 =
              let uu____342 =
                let uu____347 =
                  let uu____348 =
                    tts g.FStar_Tactics_Types.context
                      g.FStar_Tactics_Types.witness
                     in
                  FStar_Util.JsonStr uu____348  in
                ("witness", uu____347)  in
              let uu____349 =
                let uu____356 =
                  let uu____361 =
                    let uu____362 =
                      tts g.FStar_Tactics_Types.context
                        g.FStar_Tactics_Types.goal_ty
                       in
                    FStar_Util.JsonStr uu____362  in
                  ("type", uu____361)  in
                [uu____356]  in
              uu____342 :: uu____349  in
            FStar_Util.JsonAssoc uu____335  in
          ("goal", uu____334)  in
        [uu____329]  in
      ("hyps", g_binders) :: uu____322  in
    FStar_Util.JsonAssoc uu____315
  
let (ps_to_json :
  (Prims.string,FStar_Tactics_Types.proofstate)
    FStar_Pervasives_Native.tuple2 -> FStar_Util.json)
  =
  fun uu____393  ->
    match uu____393 with
    | (msg,ps) ->
        let uu____400 =
          let uu____407 =
            let uu____414 =
              let uu____421 =
                let uu____428 =
                  let uu____433 =
                    let uu____434 =
                      FStar_List.map goal_to_json
                        ps.FStar_Tactics_Types.goals
                       in
                    FStar_Util.JsonList uu____434  in
                  ("goals", uu____433)  in
                let uu____437 =
                  let uu____444 =
                    let uu____449 =
                      let uu____450 =
                        FStar_List.map goal_to_json
                          ps.FStar_Tactics_Types.smt_goals
                         in
                      FStar_Util.JsonList uu____450  in
                    ("smt-goals", uu____449)  in
                  [uu____444]  in
                uu____428 :: uu____437  in
              ("depth", (FStar_Util.JsonInt (ps.FStar_Tactics_Types.depth)))
                :: uu____421
               in
            ("label", (FStar_Util.JsonStr msg)) :: uu____414  in
          let uu____473 =
            if ps.FStar_Tactics_Types.entry_range <> FStar_Range.dummyRange
            then
              let uu____486 =
                let uu____491 =
                  FStar_Range.json_of_def_range
                    ps.FStar_Tactics_Types.entry_range
                   in
                ("location", uu____491)  in
              [uu____486]
            else []  in
          FStar_List.append uu____407 uu____473  in
        FStar_Util.JsonAssoc uu____400
  
let (dump_proofstate :
  FStar_Tactics_Types.proofstate -> Prims.string -> Prims.unit) =
  fun ps  ->
    fun msg  ->
      FStar_Options.with_saved_options
        (fun uu____517  ->
           FStar_Options.set_option "print_effect_args"
             (FStar_Options.Bool true);
           FStar_Util.print_generic "proof-state" ps_to_string ps_to_json
             (msg, ps))
  
let (print_proof_state1 : Prims.string -> Prims.unit tac) =
  fun msg  ->
    mk_tac
      (fun ps  ->
         let psc = ps.FStar_Tactics_Types.psc  in
         let subst1 = FStar_TypeChecker_Normalize.psc_subst psc  in
         (let uu____538 = FStar_Tactics_Types.subst_proof_state subst1 ps  in
          dump_cur uu____538 msg);
         FStar_Tactics_Result.Success ((), ps))
  
let (print_proof_state : Prims.string -> Prims.unit tac) =
  fun msg  ->
    mk_tac
      (fun ps  ->
         let psc = ps.FStar_Tactics_Types.psc  in
         let subst1 = FStar_TypeChecker_Normalize.psc_subst psc  in
         (let uu____554 = FStar_Tactics_Types.subst_proof_state subst1 ps  in
          dump_proofstate uu____554 msg);
         FStar_Tactics_Result.Success ((), ps))
  
let (get : FStar_Tactics_Types.proofstate tac) =
  mk_tac (fun p  -> FStar_Tactics_Result.Success (p, p)) 
let (tac_verb_dbg : Prims.bool FStar_Pervasives_Native.option FStar_ST.ref) =
  FStar_Util.mk_ref FStar_Pervasives_Native.None 
let rec (log :
  FStar_Tactics_Types.proofstate -> (Prims.unit -> Prims.unit) -> Prims.unit)
  =
  fun ps  ->
    fun f  ->
      let uu____589 = FStar_ST.op_Bang tac_verb_dbg  in
      match uu____589 with
      | FStar_Pervasives_Native.None  ->
          ((let uu____616 =
              let uu____619 =
                FStar_TypeChecker_Env.debug
                  ps.FStar_Tactics_Types.main_context
                  (FStar_Options.Other "TacVerbose")
                 in
              FStar_Pervasives_Native.Some uu____619  in
            FStar_ST.op_Colon_Equals tac_verb_dbg uu____616);
           log ps f)
      | FStar_Pervasives_Native.Some (true ) -> f ()
      | FStar_Pervasives_Native.Some (false ) -> ()
  
let mlog :
  'a . (Prims.unit -> Prims.unit) -> (Prims.unit -> 'a tac) -> 'a tac =
  fun f  -> fun cont  -> bind get (fun ps  -> log ps f; cont ()) 
let fail : 'a . Prims.string -> 'a tac =
  fun msg  ->
    mk_tac
      (fun ps  ->
         (let uu____688 =
            FStar_TypeChecker_Env.debug ps.FStar_Tactics_Types.main_context
              (FStar_Options.Other "TacFail")
             in
          if uu____688
          then dump_proofstate ps (Prims.strcat "TACTIC FAILING: " msg)
          else ());
         FStar_Tactics_Result.Failed (msg, ps))
  
let fail1 : 'Auu____693 . Prims.string -> Prims.string -> 'Auu____693 tac =
  fun msg  ->
    fun x  -> let uu____704 = FStar_Util.format1 msg x  in fail uu____704
  
let fail2 :
  'Auu____709 .
    Prims.string -> Prims.string -> Prims.string -> 'Auu____709 tac
  =
  fun msg  ->
    fun x  ->
      fun y  -> let uu____724 = FStar_Util.format2 msg x y  in fail uu____724
  
let fail3 :
  'Auu____730 .
    Prims.string ->
      Prims.string -> Prims.string -> Prims.string -> 'Auu____730 tac
  =
  fun msg  ->
    fun x  ->
      fun y  ->
        fun z  ->
          let uu____749 = FStar_Util.format3 msg x y z  in fail uu____749
  
let fail4 :
  'Auu____756 .
    Prims.string ->
      Prims.string ->
        Prims.string -> Prims.string -> Prims.string -> 'Auu____756 tac
  =
  fun msg  ->
    fun x  ->
      fun y  ->
        fun z  ->
          fun w  ->
            let uu____779 = FStar_Util.format4 msg x y z w  in fail uu____779
  
let trytac' : 'a . 'a tac -> (Prims.string,'a) FStar_Util.either tac =
  fun t  ->
    mk_tac
      (fun ps  ->
         let tx = FStar_Syntax_Unionfind.new_transaction ()  in
         let uu____809 = run t ps  in
         match uu____809 with
         | FStar_Tactics_Result.Success (a,q) ->
             (FStar_Syntax_Unionfind.commit tx;
              FStar_Tactics_Result.Success ((FStar_Util.Inr a), q))
         | FStar_Tactics_Result.Failed (m,q) ->
             (FStar_Syntax_Unionfind.rollback tx;
              (let ps1 =
                 let uu___63_833 = ps  in
                 {
                   FStar_Tactics_Types.main_context =
                     (uu___63_833.FStar_Tactics_Types.main_context);
                   FStar_Tactics_Types.main_goal =
                     (uu___63_833.FStar_Tactics_Types.main_goal);
                   FStar_Tactics_Types.all_implicits =
                     (uu___63_833.FStar_Tactics_Types.all_implicits);
                   FStar_Tactics_Types.goals =
                     (uu___63_833.FStar_Tactics_Types.goals);
                   FStar_Tactics_Types.smt_goals =
                     (uu___63_833.FStar_Tactics_Types.smt_goals);
                   FStar_Tactics_Types.depth =
                     (uu___63_833.FStar_Tactics_Types.depth);
                   FStar_Tactics_Types.__dump =
                     (uu___63_833.FStar_Tactics_Types.__dump);
                   FStar_Tactics_Types.psc =
                     (uu___63_833.FStar_Tactics_Types.psc);
                   FStar_Tactics_Types.entry_range =
                     (uu___63_833.FStar_Tactics_Types.entry_range);
                   FStar_Tactics_Types.guard_policy =
                     (uu___63_833.FStar_Tactics_Types.guard_policy);
                   FStar_Tactics_Types.freshness =
                     (q.FStar_Tactics_Types.freshness)
                 }  in
               FStar_Tactics_Result.Success ((FStar_Util.Inl m), ps1))))
  
let trytac : 'a . 'a tac -> 'a FStar_Pervasives_Native.option tac =
  fun t  ->
    let uu____857 = trytac' t  in
    bind uu____857
      (fun r  ->
         match r with
         | FStar_Util.Inr v1 -> ret (FStar_Pervasives_Native.Some v1)
         | FStar_Util.Inl uu____884 -> ret FStar_Pervasives_Native.None)
  
let trytac_exn : 'a . 'a tac -> 'a FStar_Pervasives_Native.option tac =
  fun t  ->
    mk_tac
      (fun ps  ->
         try let uu____917 = trytac t  in run uu____917 ps
         with
         | FStar_Errors.Err (uu____933,msg) ->
             (log ps
                (fun uu____937  ->
                   FStar_Util.print1 "trytac_exn error: (%s)" msg);
              FStar_Tactics_Result.Success (FStar_Pervasives_Native.None, ps))
         | FStar_Errors.Error (uu____942,msg,uu____944) ->
             (log ps
                (fun uu____947  ->
                   FStar_Util.print1 "trytac_exn error: (%s)" msg);
              FStar_Tactics_Result.Success (FStar_Pervasives_Native.None, ps)))
  
let wrap_err : 'a . Prims.string -> 'a tac -> 'a tac =
  fun pref  ->
    fun t  ->
      mk_tac
        (fun ps  ->
           let uu____975 = run t ps  in
           match uu____975 with
           | FStar_Tactics_Result.Success (a,q) ->
               FStar_Tactics_Result.Success (a, q)
           | FStar_Tactics_Result.Failed (msg,q) ->
               FStar_Tactics_Result.Failed
                 ((Prims.strcat pref (Prims.strcat ": " msg)), q))
  
let (set : FStar_Tactics_Types.proofstate -> Prims.unit tac) =
  fun p  -> mk_tac (fun uu____992  -> FStar_Tactics_Result.Success ((), p)) 
let (__do_unify :
  env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool tac)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let debug_on uu____1009 =
          let uu____1010 =
            FStar_Options.set_options FStar_Options.Set
              "--debug_level Rel --debug_level RelCheck"
             in
          ()  in
        let debug_off uu____1014 =
          let uu____1015 = FStar_Options.set_options FStar_Options.Reset ""
             in
          ()  in
        (let uu____1017 =
           FStar_TypeChecker_Env.debug env (FStar_Options.Other "1346")  in
         if uu____1017
         then
           (debug_on ();
            (let uu____1019 = FStar_Syntax_Print.term_to_string t1  in
             let uu____1020 = FStar_Syntax_Print.term_to_string t2  in
             FStar_Util.print2 "%%%%%%%%do_unify %s =? %s\n" uu____1019
               uu____1020))
         else ());
        (try
           let res = FStar_TypeChecker_Rel.teq_nosmt env t1 t2  in
           debug_off ();
           (let uu____1034 =
              FStar_TypeChecker_Env.debug env (FStar_Options.Other "1346")
               in
            if uu____1034
            then
              let uu____1035 = FStar_Util.string_of_bool res  in
              let uu____1036 = FStar_Syntax_Print.term_to_string t1  in
              let uu____1037 = FStar_Syntax_Print.term_to_string t2  in
              FStar_Util.print3 "%%%%%%%%do_unify (RESULT %s) %s =? %s\n"
                uu____1035 uu____1036 uu____1037
            else ());
           ret res
         with
         | FStar_Errors.Err (uu____1046,msg) ->
             (debug_off ();
              mlog
                (fun uu____1050  ->
                   FStar_Util.print1 ">> do_unify error, (%s)\n" msg)
                (fun uu____1052  -> ret false))
         | FStar_Errors.Error (uu____1053,msg,r) ->
             (debug_off ();
              mlog
                (fun uu____1059  ->
                   let uu____1060 = FStar_Range.string_of_range r  in
                   FStar_Util.print2 ">> do_unify error, (%s) at (%s)\n" msg
                     uu____1060) (fun uu____1062  -> ret false)))
  
let (do_unify :
  env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool tac)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____1076 = __do_unify env t1 t2  in
        bind uu____1076
          (fun b  ->
             if Prims.op_Negation b
             then
               let t11 = FStar_TypeChecker_Normalize.normalize [] env t1  in
               let t21 = FStar_TypeChecker_Normalize.normalize [] env t2  in
               __do_unify env t11 t21
             else ret b)
  
let (trysolve :
  FStar_Tactics_Types.goal -> FStar_Syntax_Syntax.term -> Prims.bool tac) =
  fun goal  ->
    fun solution  ->
      do_unify goal.FStar_Tactics_Types.context solution
        goal.FStar_Tactics_Types.witness
  
let (__dismiss : Prims.unit tac) =
  bind get
    (fun p  ->
       let uu____1103 =
         let uu___68_1104 = p  in
         let uu____1105 = FStar_List.tl p.FStar_Tactics_Types.goals  in
         {
           FStar_Tactics_Types.main_context =
             (uu___68_1104.FStar_Tactics_Types.main_context);
           FStar_Tactics_Types.main_goal =
             (uu___68_1104.FStar_Tactics_Types.main_goal);
           FStar_Tactics_Types.all_implicits =
             (uu___68_1104.FStar_Tactics_Types.all_implicits);
           FStar_Tactics_Types.goals = uu____1105;
           FStar_Tactics_Types.smt_goals =
             (uu___68_1104.FStar_Tactics_Types.smt_goals);
           FStar_Tactics_Types.depth =
             (uu___68_1104.FStar_Tactics_Types.depth);
           FStar_Tactics_Types.__dump =
             (uu___68_1104.FStar_Tactics_Types.__dump);
           FStar_Tactics_Types.psc = (uu___68_1104.FStar_Tactics_Types.psc);
           FStar_Tactics_Types.entry_range =
             (uu___68_1104.FStar_Tactics_Types.entry_range);
           FStar_Tactics_Types.guard_policy =
             (uu___68_1104.FStar_Tactics_Types.guard_policy);
           FStar_Tactics_Types.freshness =
             (uu___68_1104.FStar_Tactics_Types.freshness)
         }  in
       set uu____1103)
  
let (dismiss : Prims.unit tac) =
  bind get
    (fun p  ->
       match p.FStar_Tactics_Types.goals with
       | [] -> fail "dismiss: no more goals"
       | uu____1116 -> __dismiss)
  
let (solve :
  FStar_Tactics_Types.goal -> FStar_Syntax_Syntax.term -> Prims.unit tac) =
  fun goal  ->
    fun solution  ->
      let uu____1129 = trysolve goal solution  in
      bind uu____1129
        (fun b  ->
           if b
           then __dismiss
           else
             (let uu____1137 =
                let uu____1138 =
                  tts goal.FStar_Tactics_Types.context solution  in
                let uu____1139 =
                  tts goal.FStar_Tactics_Types.context
                    goal.FStar_Tactics_Types.witness
                   in
                let uu____1140 =
                  tts goal.FStar_Tactics_Types.context
                    goal.FStar_Tactics_Types.goal_ty
                   in
                FStar_Util.format3 "%s does not solve %s : %s" uu____1138
                  uu____1139 uu____1140
                 in
              fail uu____1137))
  
let (dismiss_all : Prims.unit tac) =
  bind get
    (fun p  ->
       set
         (let uu___69_1147 = p  in
          {
            FStar_Tactics_Types.main_context =
              (uu___69_1147.FStar_Tactics_Types.main_context);
            FStar_Tactics_Types.main_goal =
              (uu___69_1147.FStar_Tactics_Types.main_goal);
            FStar_Tactics_Types.all_implicits =
              (uu___69_1147.FStar_Tactics_Types.all_implicits);
            FStar_Tactics_Types.goals = [];
            FStar_Tactics_Types.smt_goals =
              (uu___69_1147.FStar_Tactics_Types.smt_goals);
            FStar_Tactics_Types.depth =
              (uu___69_1147.FStar_Tactics_Types.depth);
            FStar_Tactics_Types.__dump =
              (uu___69_1147.FStar_Tactics_Types.__dump);
            FStar_Tactics_Types.psc = (uu___69_1147.FStar_Tactics_Types.psc);
            FStar_Tactics_Types.entry_range =
              (uu___69_1147.FStar_Tactics_Types.entry_range);
            FStar_Tactics_Types.guard_policy =
              (uu___69_1147.FStar_Tactics_Types.guard_policy);
            FStar_Tactics_Types.freshness =
              (uu___69_1147.FStar_Tactics_Types.freshness)
          }))
  
let (nwarn : Prims.int FStar_ST.ref) =
  FStar_Util.mk_ref (Prims.parse_int "0") 
let (check_valid_goal : FStar_Tactics_Types.goal -> Prims.unit) =
  fun g  ->
    let uu____1164 = FStar_Options.defensive ()  in
    if uu____1164
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
        let uu____1176 = FStar_TypeChecker_Env.pop_bv e  in
        match uu____1176 with
        | FStar_Pervasives_Native.None  -> b3
        | FStar_Pervasives_Native.Some (bv,e1) ->
            let b4 =
              b3 &&
                (FStar_TypeChecker_Env.closed e1 bv.FStar_Syntax_Syntax.sort)
               in
            aux b4 e1
         in
      let uu____1194 =
        (let uu____1197 = aux b2 env  in Prims.op_Negation uu____1197) &&
          (let uu____1199 = FStar_ST.op_Bang nwarn  in
           uu____1199 < (Prims.parse_int "5"))
         in
      (if uu____1194
       then
         ((let uu____1220 =
             let uu____1225 =
               let uu____1226 = goal_to_string g  in
               FStar_Util.format1
                 "The following goal is ill-formed. Keeping calm and carrying on...\n<%s>\n\n"
                 uu____1226
                in
             (FStar_Errors.Warning_IllFormedGoal, uu____1225)  in
           FStar_Errors.log_issue
             (g.FStar_Tactics_Types.goal_ty).FStar_Syntax_Syntax.pos
             uu____1220);
          (let uu____1227 =
             let uu____1228 = FStar_ST.op_Bang nwarn  in
             uu____1228 + (Prims.parse_int "1")  in
           FStar_ST.op_Colon_Equals nwarn uu____1227))
       else ())
    else ()
  
let (add_goals : FStar_Tactics_Types.goal Prims.list -> Prims.unit tac) =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___70_1286 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___70_1286.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___70_1286.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___70_1286.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (FStar_List.append gs p.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___70_1286.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___70_1286.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___70_1286.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___70_1286.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___70_1286.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___70_1286.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___70_1286.FStar_Tactics_Types.freshness)
            }))
  
let (add_smt_goals : FStar_Tactics_Types.goal Prims.list -> Prims.unit tac) =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___71_1304 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___71_1304.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___71_1304.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___71_1304.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___71_1304.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (FStar_List.append gs p.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___71_1304.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___71_1304.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___71_1304.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___71_1304.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___71_1304.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___71_1304.FStar_Tactics_Types.freshness)
            }))
  
let (push_goals : FStar_Tactics_Types.goal Prims.list -> Prims.unit tac) =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___72_1322 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___72_1322.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___72_1322.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___72_1322.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (FStar_List.append p.FStar_Tactics_Types.goals gs);
              FStar_Tactics_Types.smt_goals =
                (uu___72_1322.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___72_1322.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___72_1322.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___72_1322.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___72_1322.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___72_1322.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___72_1322.FStar_Tactics_Types.freshness)
            }))
  
let (push_smt_goals : FStar_Tactics_Types.goal Prims.list -> Prims.unit tac)
  =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___73_1340 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___73_1340.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___73_1340.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___73_1340.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___73_1340.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (FStar_List.append p.FStar_Tactics_Types.smt_goals gs);
              FStar_Tactics_Types.depth =
                (uu___73_1340.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___73_1340.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___73_1340.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___73_1340.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___73_1340.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___73_1340.FStar_Tactics_Types.freshness)
            }))
  
let (replace_cur : FStar_Tactics_Types.goal -> Prims.unit tac) =
  fun g  -> bind __dismiss (fun uu____1349  -> add_goals [g]) 
let (add_implicits : implicits -> Prims.unit tac) =
  fun i  ->
    bind get
      (fun p  ->
         set
           (let uu___74_1361 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___74_1361.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___74_1361.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (FStar_List.append i p.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___74_1361.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___74_1361.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___74_1361.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___74_1361.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___74_1361.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___74_1361.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___74_1361.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___74_1361.FStar_Tactics_Types.freshness)
            }))
  
let (new_uvar :
  Prims.string ->
    env -> FStar_Reflection_Data.typ -> FStar_Syntax_Syntax.term tac)
  =
  fun reason  ->
    fun env  ->
      fun typ  ->
        let uu____1387 =
          FStar_TypeChecker_Util.new_implicit_var reason
            typ.FStar_Syntax_Syntax.pos env typ
           in
        match uu____1387 with
        | (u,uu____1403,g_u) ->
            let uu____1417 =
              add_implicits g_u.FStar_TypeChecker_Env.implicits  in
            bind uu____1417 (fun uu____1421  -> ret u)
  
let (is_true : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____1425 = FStar_Syntax_Util.un_squash t  in
    match uu____1425 with
    | FStar_Pervasives_Native.Some t' ->
        let uu____1435 =
          let uu____1436 = FStar_Syntax_Subst.compress t'  in
          uu____1436.FStar_Syntax_Syntax.n  in
        (match uu____1435 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.true_lid
         | uu____1440 -> false)
    | uu____1441 -> false
  
let (is_false : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____1449 = FStar_Syntax_Util.un_squash t  in
    match uu____1449 with
    | FStar_Pervasives_Native.Some t' ->
        let uu____1459 =
          let uu____1460 = FStar_Syntax_Subst.compress t'  in
          uu____1460.FStar_Syntax_Syntax.n  in
        (match uu____1459 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.false_lid
         | uu____1464 -> false)
    | uu____1465 -> false
  
let (cur_goal : FStar_Tactics_Types.goal tac) =
  bind get
    (fun p  ->
       match p.FStar_Tactics_Types.goals with
       | [] -> fail "No more goals (1)"
       | hd1::tl1 -> ret hd1)
  
let (tadmit : Prims.unit tac) =
  let uu____1484 =
    bind cur_goal
      (fun g  ->
         (let uu____1491 =
            let uu____1496 =
              let uu____1497 = goal_to_string g  in
              FStar_Util.format1 "Tactics admitted goal <%s>\n\n" uu____1497
               in
            (FStar_Errors.Warning_TacAdmit, uu____1496)  in
          FStar_Errors.log_issue
            (g.FStar_Tactics_Types.goal_ty).FStar_Syntax_Syntax.pos
            uu____1491);
         solve g FStar_Syntax_Util.exp_unit)
     in
  FStar_All.pipe_left (wrap_err "tadmit") uu____1484 
let (fresh : FStar_BigInt.bigint tac) =
  bind get
    (fun ps  ->
       let n1 = ps.FStar_Tactics_Types.freshness  in
       let ps1 =
         let uu___75_1513 = ps  in
         {
           FStar_Tactics_Types.main_context =
             (uu___75_1513.FStar_Tactics_Types.main_context);
           FStar_Tactics_Types.main_goal =
             (uu___75_1513.FStar_Tactics_Types.main_goal);
           FStar_Tactics_Types.all_implicits =
             (uu___75_1513.FStar_Tactics_Types.all_implicits);
           FStar_Tactics_Types.goals =
             (uu___75_1513.FStar_Tactics_Types.goals);
           FStar_Tactics_Types.smt_goals =
             (uu___75_1513.FStar_Tactics_Types.smt_goals);
           FStar_Tactics_Types.depth =
             (uu___75_1513.FStar_Tactics_Types.depth);
           FStar_Tactics_Types.__dump =
             (uu___75_1513.FStar_Tactics_Types.__dump);
           FStar_Tactics_Types.psc = (uu___75_1513.FStar_Tactics_Types.psc);
           FStar_Tactics_Types.entry_range =
             (uu___75_1513.FStar_Tactics_Types.entry_range);
           FStar_Tactics_Types.guard_policy =
             (uu___75_1513.FStar_Tactics_Types.guard_policy);
           FStar_Tactics_Types.freshness = (n1 + (Prims.parse_int "1"))
         }  in
       let uu____1514 = set ps1  in
       bind uu____1514
         (fun uu____1519  ->
            let uu____1520 = FStar_BigInt.of_int_fs n1  in ret uu____1520))
  
let (ngoals : FStar_BigInt.bigint tac) =
  bind get
    (fun ps  ->
       let n1 = FStar_List.length ps.FStar_Tactics_Types.goals  in
       let uu____1530 = FStar_BigInt.of_int_fs n1  in ret uu____1530)
  
let (ngoals_smt : FStar_BigInt.bigint tac) =
  bind get
    (fun ps  ->
       let n1 = FStar_List.length ps.FStar_Tactics_Types.smt_goals  in
       let uu____1546 = FStar_BigInt.of_int_fs n1  in ret uu____1546)
  
let (is_guard : Prims.bool tac) =
  bind cur_goal (fun g  -> ret g.FStar_Tactics_Types.is_guard) 
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
            let uu____1578 = env.FStar_TypeChecker_Env.universe_of env phi
               in
            FStar_Syntax_Util.mk_squash uu____1578 phi  in
          let uu____1579 = new_uvar reason env typ  in
          bind uu____1579
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
             (fun uu____1624  ->
                let uu____1625 = tts e t  in
                FStar_Util.print1 "Tac> __tc(%s)\n" uu____1625)
             (fun uu____1627  ->
                try
                  let uu____1647 =
                    (ps.FStar_Tactics_Types.main_context).FStar_TypeChecker_Env.type_of
                      e t
                     in
                  ret uu____1647
                with
                | FStar_Errors.Err (uu____1674,msg) ->
                    let uu____1676 = tts e t  in
                    let uu____1677 =
                      let uu____1678 = FStar_TypeChecker_Env.all_binders e
                         in
                      FStar_All.pipe_right uu____1678
                        (FStar_Syntax_Print.binders_to_string ", ")
                       in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____1676 uu____1677 msg
                | FStar_Errors.Error (uu____1685,msg,uu____1687) ->
                    let uu____1688 = tts e t  in
                    let uu____1689 =
                      let uu____1690 = FStar_TypeChecker_Env.all_binders e
                         in
                      FStar_All.pipe_right uu____1690
                        (FStar_Syntax_Print.binders_to_string ", ")
                       in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____1688 uu____1689 msg))
  
let (istrivial : env -> FStar_Syntax_Syntax.term -> Prims.bool) =
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
  
let (get_guard_policy : FStar_Tactics_Types.guard_policy tac) =
  bind get (fun ps  -> ret ps.FStar_Tactics_Types.guard_policy) 
let (set_guard_policy : FStar_Tactics_Types.guard_policy -> Prims.unit tac) =
  fun pol  ->
    bind get
      (fun ps  ->
         set
           (let uu___78_1724 = ps  in
            {
              FStar_Tactics_Types.main_context =
                (uu___78_1724.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___78_1724.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___78_1724.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___78_1724.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___78_1724.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___78_1724.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___78_1724.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___78_1724.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___78_1724.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy = pol;
              FStar_Tactics_Types.freshness =
                (uu___78_1724.FStar_Tactics_Types.freshness)
            }))
  
let with_policy : 'a . FStar_Tactics_Types.guard_policy -> 'a tac -> 'a tac =
  fun pol  ->
    fun t  ->
      bind get_guard_policy
        (fun old_pol  ->
           let uu____1746 = set_guard_policy pol  in
           bind uu____1746
             (fun uu____1750  ->
                bind t
                  (fun r  ->
                     let uu____1754 = set_guard_policy old_pol  in
                     bind uu____1754 (fun uu____1758  -> ret r))))
  
let (proc_guard :
  Prims.string ->
    env ->
      FStar_TypeChecker_Env.guard_t ->
        FStar_Options.optionstate -> Prims.unit tac)
  =
  fun reason  ->
    fun e  ->
      fun g  ->
        fun opts  ->
          let uu____1775 =
            let uu____1776 = FStar_TypeChecker_Rel.simplify_guard e g  in
            uu____1776.FStar_TypeChecker_Env.guard_f  in
          match uu____1775 with
          | FStar_TypeChecker_Common.Trivial  -> ret ()
          | FStar_TypeChecker_Common.NonTrivial f ->
              let uu____1780 = istrivial e f  in
              if uu____1780
              then ret ()
              else
                bind get
                  (fun ps  ->
                     match ps.FStar_Tactics_Types.guard_policy with
                     | FStar_Tactics_Types.Drop  -> ret ()
                     | FStar_Tactics_Types.Goal  ->
                         let uu____1788 = mk_irrelevant_goal reason e f opts
                            in
                         bind uu____1788
                           (fun goal  ->
                              let goal1 =
                                let uu___79_1795 = goal  in
                                {
                                  FStar_Tactics_Types.context =
                                    (uu___79_1795.FStar_Tactics_Types.context);
                                  FStar_Tactics_Types.witness =
                                    (uu___79_1795.FStar_Tactics_Types.witness);
                                  FStar_Tactics_Types.goal_ty =
                                    (uu___79_1795.FStar_Tactics_Types.goal_ty);
                                  FStar_Tactics_Types.opts =
                                    (uu___79_1795.FStar_Tactics_Types.opts);
                                  FStar_Tactics_Types.is_guard = true
                                }  in
                              push_goals [goal1])
                     | FStar_Tactics_Types.SMT  ->
                         let uu____1796 = mk_irrelevant_goal reason e f opts
                            in
                         bind uu____1796
                           (fun goal  ->
                              let goal1 =
                                let uu___80_1803 = goal  in
                                {
                                  FStar_Tactics_Types.context =
                                    (uu___80_1803.FStar_Tactics_Types.context);
                                  FStar_Tactics_Types.witness =
                                    (uu___80_1803.FStar_Tactics_Types.witness);
                                  FStar_Tactics_Types.goal_ty =
                                    (uu___80_1803.FStar_Tactics_Types.goal_ty);
                                  FStar_Tactics_Types.opts =
                                    (uu___80_1803.FStar_Tactics_Types.opts);
                                  FStar_Tactics_Types.is_guard = true
                                }  in
                              push_smt_goals [goal1])
                     | FStar_Tactics_Types.Force  ->
                         (try
                            let uu____1811 =
                              let uu____1812 =
                                let uu____1813 =
                                  FStar_TypeChecker_Rel.discharge_guard_no_smt
                                    e g
                                   in
                                FStar_All.pipe_left
                                  FStar_TypeChecker_Rel.is_trivial uu____1813
                                 in
                              Prims.op_Negation uu____1812  in
                            if uu____1811
                            then
                              mlog
                                (fun uu____1818  ->
                                   let uu____1819 =
                                     FStar_TypeChecker_Rel.guard_to_string e
                                       g
                                      in
                                   FStar_Util.print1 "guard = %s\n"
                                     uu____1819)
                                (fun uu____1821  ->
                                   fail1 "Forcing the guard failed %s)"
                                     reason)
                            else ret ()
                          with
                          | uu____1828 ->
                              mlog
                                (fun uu____1831  ->
                                   let uu____1832 =
                                     FStar_TypeChecker_Rel.guard_to_string e
                                       g
                                      in
                                   FStar_Util.print1 "guard = %s\n"
                                     uu____1832)
                                (fun uu____1834  ->
                                   fail1 "Forcing the guard failed (%s)"
                                     reason)))
  
let (tc : FStar_Syntax_Syntax.term -> FStar_Reflection_Data.typ tac) =
  fun t  ->
    let uu____1842 =
      bind cur_goal
        (fun goal  ->
           let uu____1848 = __tc goal.FStar_Tactics_Types.context t  in
           bind uu____1848
             (fun uu____1868  ->
                match uu____1868 with
                | (t1,typ,guard) ->
                    let uu____1880 =
                      proc_guard "tc" goal.FStar_Tactics_Types.context guard
                        goal.FStar_Tactics_Types.opts
                       in
                    bind uu____1880 (fun uu____1884  -> ret typ)))
       in
    FStar_All.pipe_left (wrap_err "tc") uu____1842
  
let (add_irrelevant_goal :
  Prims.string ->
    env ->
      FStar_Reflection_Data.typ ->
        FStar_Options.optionstate -> Prims.unit tac)
  =
  fun reason  ->
    fun env  ->
      fun phi  ->
        fun opts  ->
          let uu____1905 = mk_irrelevant_goal reason env phi opts  in
          bind uu____1905 (fun goal  -> add_goals [goal])
  
let (trivial : Prims.unit tac) =
  bind cur_goal
    (fun goal  ->
       let uu____1917 =
         istrivial goal.FStar_Tactics_Types.context
           goal.FStar_Tactics_Types.goal_ty
          in
       if uu____1917
       then solve goal FStar_Syntax_Util.exp_unit
       else
         (let uu____1921 =
            tts goal.FStar_Tactics_Types.context
              goal.FStar_Tactics_Types.goal_ty
             in
          fail1 "Not a trivial goal: %s" uu____1921))
  
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
          let uu____1942 =
            let uu____1943 = FStar_TypeChecker_Rel.simplify_guard e g  in
            uu____1943.FStar_TypeChecker_Env.guard_f  in
          match uu____1942 with
          | FStar_TypeChecker_Common.Trivial  ->
              ret FStar_Pervasives_Native.None
          | FStar_TypeChecker_Common.NonTrivial f ->
              let uu____1951 = istrivial e f  in
              if uu____1951
              then ret FStar_Pervasives_Native.None
              else
                (let uu____1959 = mk_irrelevant_goal reason e f opts  in
                 bind uu____1959
                   (fun goal  ->
                      ret
                        (FStar_Pervasives_Native.Some
                           (let uu___83_1969 = goal  in
                            {
                              FStar_Tactics_Types.context =
                                (uu___83_1969.FStar_Tactics_Types.context);
                              FStar_Tactics_Types.witness =
                                (uu___83_1969.FStar_Tactics_Types.witness);
                              FStar_Tactics_Types.goal_ty =
                                (uu___83_1969.FStar_Tactics_Types.goal_ty);
                              FStar_Tactics_Types.opts =
                                (uu___83_1969.FStar_Tactics_Types.opts);
                              FStar_Tactics_Types.is_guard = true
                            }))))
  
let (smt : Prims.unit tac) =
  bind cur_goal
    (fun g  ->
       let uu____1977 = is_irrelevant g  in
       if uu____1977
       then bind __dismiss (fun uu____1981  -> add_smt_goals [g])
       else
         (let uu____1983 =
            tts g.FStar_Tactics_Types.context g.FStar_Tactics_Types.goal_ty
             in
          fail1 "goal is not irrelevant: cannot dispatch to smt (%s)"
            uu____1983))
  
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
             let uu____2024 =
               try
                 let uu____2058 =
                   let uu____2067 = FStar_BigInt.to_int_fs n1  in
                   FStar_List.splitAt uu____2067 p.FStar_Tactics_Types.goals
                    in
                 ret uu____2058
               with | uu____2089 -> fail "divide: not enough goals"  in
             bind uu____2024
               (fun uu____2116  ->
                  match uu____2116 with
                  | (lgs,rgs) ->
                      let lp =
                        let uu___84_2142 = p  in
                        {
                          FStar_Tactics_Types.main_context =
                            (uu___84_2142.FStar_Tactics_Types.main_context);
                          FStar_Tactics_Types.main_goal =
                            (uu___84_2142.FStar_Tactics_Types.main_goal);
                          FStar_Tactics_Types.all_implicits =
                            (uu___84_2142.FStar_Tactics_Types.all_implicits);
                          FStar_Tactics_Types.goals = lgs;
                          FStar_Tactics_Types.smt_goals = [];
                          FStar_Tactics_Types.depth =
                            (uu___84_2142.FStar_Tactics_Types.depth);
                          FStar_Tactics_Types.__dump =
                            (uu___84_2142.FStar_Tactics_Types.__dump);
                          FStar_Tactics_Types.psc =
                            (uu___84_2142.FStar_Tactics_Types.psc);
                          FStar_Tactics_Types.entry_range =
                            (uu___84_2142.FStar_Tactics_Types.entry_range);
                          FStar_Tactics_Types.guard_policy =
                            (uu___84_2142.FStar_Tactics_Types.guard_policy);
                          FStar_Tactics_Types.freshness =
                            (uu___84_2142.FStar_Tactics_Types.freshness)
                        }  in
                      let rp =
                        let uu___85_2144 = p  in
                        {
                          FStar_Tactics_Types.main_context =
                            (uu___85_2144.FStar_Tactics_Types.main_context);
                          FStar_Tactics_Types.main_goal =
                            (uu___85_2144.FStar_Tactics_Types.main_goal);
                          FStar_Tactics_Types.all_implicits =
                            (uu___85_2144.FStar_Tactics_Types.all_implicits);
                          FStar_Tactics_Types.goals = rgs;
                          FStar_Tactics_Types.smt_goals = [];
                          FStar_Tactics_Types.depth =
                            (uu___85_2144.FStar_Tactics_Types.depth);
                          FStar_Tactics_Types.__dump =
                            (uu___85_2144.FStar_Tactics_Types.__dump);
                          FStar_Tactics_Types.psc =
                            (uu___85_2144.FStar_Tactics_Types.psc);
                          FStar_Tactics_Types.entry_range =
                            (uu___85_2144.FStar_Tactics_Types.entry_range);
                          FStar_Tactics_Types.guard_policy =
                            (uu___85_2144.FStar_Tactics_Types.guard_policy);
                          FStar_Tactics_Types.freshness =
                            (uu___85_2144.FStar_Tactics_Types.freshness)
                        }  in
                      let uu____2145 = set lp  in
                      bind uu____2145
                        (fun uu____2153  ->
                           bind l
                             (fun a  ->
                                bind get
                                  (fun lp'  ->
                                     let uu____2167 = set rp  in
                                     bind uu____2167
                                       (fun uu____2175  ->
                                          bind r
                                            (fun b  ->
                                               bind get
                                                 (fun rp'  ->
                                                    let p' =
                                                      let uu___86_2191 = p
                                                         in
                                                      {
                                                        FStar_Tactics_Types.main_context
                                                          =
                                                          (uu___86_2191.FStar_Tactics_Types.main_context);
                                                        FStar_Tactics_Types.main_goal
                                                          =
                                                          (uu___86_2191.FStar_Tactics_Types.main_goal);
                                                        FStar_Tactics_Types.all_implicits
                                                          =
                                                          (uu___86_2191.FStar_Tactics_Types.all_implicits);
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
                                                          (uu___86_2191.FStar_Tactics_Types.depth);
                                                        FStar_Tactics_Types.__dump
                                                          =
                                                          (uu___86_2191.FStar_Tactics_Types.__dump);
                                                        FStar_Tactics_Types.psc
                                                          =
                                                          (uu___86_2191.FStar_Tactics_Types.psc);
                                                        FStar_Tactics_Types.entry_range
                                                          =
                                                          (uu___86_2191.FStar_Tactics_Types.entry_range);
                                                        FStar_Tactics_Types.guard_policy
                                                          =
                                                          (uu___86_2191.FStar_Tactics_Types.guard_policy);
                                                        FStar_Tactics_Types.freshness
                                                          =
                                                          (uu___86_2191.FStar_Tactics_Types.freshness)
                                                      }  in
                                                    let uu____2192 = set p'
                                                       in
                                                    bind uu____2192
                                                      (fun uu____2200  ->
                                                         ret (a, b))))))))))
  
let focus : 'a . 'a tac -> 'a tac =
  fun f  ->
    let uu____2218 = divide FStar_BigInt.one f idtac  in
    bind uu____2218
      (fun uu____2231  -> match uu____2231 with | (a,()) -> ret a)
  
let rec map : 'a . 'a tac -> 'a Prims.list tac =
  fun tau  ->
    bind get
      (fun p  ->
         match p.FStar_Tactics_Types.goals with
         | [] -> ret []
         | uu____2265::uu____2266 ->
             let uu____2269 =
               let uu____2278 = map tau  in
               divide FStar_BigInt.one tau uu____2278  in
             bind uu____2269
               (fun uu____2296  ->
                  match uu____2296 with | (h,t) -> ret (h :: t)))
  
let (seq : Prims.unit tac -> Prims.unit tac -> Prims.unit tac) =
  fun t1  ->
    fun t2  ->
      let uu____2333 =
        bind t1
          (fun uu____2338  ->
             let uu____2339 = map t2  in
             bind uu____2339 (fun uu____2347  -> ret ()))
         in
      focus uu____2333
  
let (intro : FStar_Syntax_Syntax.binder tac) =
  let uu____2354 =
    bind cur_goal
      (fun goal  ->
         let uu____2363 =
           FStar_Syntax_Util.arrow_one goal.FStar_Tactics_Types.goal_ty  in
         match uu____2363 with
         | FStar_Pervasives_Native.Some (b,c) ->
             let uu____2378 =
               let uu____2379 = FStar_Syntax_Util.is_total_comp c  in
               Prims.op_Negation uu____2379  in
             if uu____2378
             then fail "Codomain is effectful"
             else
               (let env' =
                  FStar_TypeChecker_Env.push_binders
                    goal.FStar_Tactics_Types.context [b]
                   in
                let typ' = comp_to_typ c  in
                let uu____2385 = new_uvar "intro" env' typ'  in
                bind uu____2385
                  (fun u  ->
                     let uu____2391 =
                       let uu____2394 =
                         FStar_Syntax_Util.abs [b] u
                           FStar_Pervasives_Native.None
                          in
                       trysolve goal uu____2394  in
                     bind uu____2391
                       (fun bb  ->
                          if bb
                          then
                            let uu____2400 =
                              let uu____2403 =
                                let uu___89_2404 = goal  in
                                let uu____2405 = bnorm env' u  in
                                let uu____2406 = bnorm env' typ'  in
                                {
                                  FStar_Tactics_Types.context = env';
                                  FStar_Tactics_Types.witness = uu____2405;
                                  FStar_Tactics_Types.goal_ty = uu____2406;
                                  FStar_Tactics_Types.opts =
                                    (uu___89_2404.FStar_Tactics_Types.opts);
                                  FStar_Tactics_Types.is_guard =
                                    (uu___89_2404.FStar_Tactics_Types.is_guard)
                                }  in
                              replace_cur uu____2403  in
                            bind uu____2400 (fun uu____2408  -> ret b)
                          else fail "unification failed")))
         | FStar_Pervasives_Native.None  ->
             let uu____2414 =
               tts goal.FStar_Tactics_Types.context
                 goal.FStar_Tactics_Types.goal_ty
                in
             fail1 "goal is not an arrow (%s)" uu____2414)
     in
  FStar_All.pipe_left (wrap_err "intro") uu____2354 
let (intro_rec :
  (FStar_Syntax_Syntax.binder,FStar_Syntax_Syntax.binder)
    FStar_Pervasives_Native.tuple2 tac)
  =
  bind cur_goal
    (fun goal  ->
       FStar_Util.print_string
         "WARNING (intro_rec): calling this is known to cause normalizer loops\n";
       FStar_Util.print_string
         "WARNING (intro_rec): proceed at your own risk...\n";
       (let uu____2445 =
          FStar_Syntax_Util.arrow_one goal.FStar_Tactics_Types.goal_ty  in
        match uu____2445 with
        | FStar_Pervasives_Native.Some (b,c) ->
            let uu____2464 =
              let uu____2465 = FStar_Syntax_Util.is_total_comp c  in
              Prims.op_Negation uu____2465  in
            if uu____2464
            then fail "Codomain is effectful"
            else
              (let bv =
                 FStar_Syntax_Syntax.gen_bv "__recf"
                   FStar_Pervasives_Native.None
                   goal.FStar_Tactics_Types.goal_ty
                  in
               let bs =
                 let uu____2481 = FStar_Syntax_Syntax.mk_binder bv  in
                 [uu____2481; b]  in
               let env' =
                 FStar_TypeChecker_Env.push_binders
                   goal.FStar_Tactics_Types.context bs
                  in
               let uu____2483 =
                 let uu____2486 = comp_to_typ c  in
                 new_uvar "intro_rec" env' uu____2486  in
               bind uu____2483
                 (fun u  ->
                    let lb =
                      let uu____2501 =
                        FStar_Syntax_Util.abs [b] u
                          FStar_Pervasives_Native.None
                         in
                      FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl bv) []
                        goal.FStar_Tactics_Types.goal_ty
                        FStar_Parser_Const.effect_Tot_lid uu____2501 []
                        FStar_Range.dummyRange
                       in
                    let body = FStar_Syntax_Syntax.bv_to_name bv  in
                    let uu____2507 =
                      FStar_Syntax_Subst.close_let_rec [lb] body  in
                    match uu____2507 with
                    | (lbs,body1) ->
                        let tm =
                          FStar_Syntax_Syntax.mk
                            (FStar_Syntax_Syntax.Tm_let ((true, lbs), body1))
                            FStar_Pervasives_Native.None
                            (goal.FStar_Tactics_Types.witness).FStar_Syntax_Syntax.pos
                           in
                        let uu____2537 = trysolve goal tm  in
                        bind uu____2537
                          (fun bb  ->
                             if bb
                             then
                               let uu____2553 =
                                 let uu____2556 =
                                   let uu___90_2557 = goal  in
                                   let uu____2558 = bnorm env' u  in
                                   let uu____2559 =
                                     let uu____2560 = comp_to_typ c  in
                                     bnorm env' uu____2560  in
                                   {
                                     FStar_Tactics_Types.context = env';
                                     FStar_Tactics_Types.witness = uu____2558;
                                     FStar_Tactics_Types.goal_ty = uu____2559;
                                     FStar_Tactics_Types.opts =
                                       (uu___90_2557.FStar_Tactics_Types.opts);
                                     FStar_Tactics_Types.is_guard =
                                       (uu___90_2557.FStar_Tactics_Types.is_guard)
                                   }  in
                                 replace_cur uu____2556  in
                               bind uu____2553
                                 (fun uu____2567  ->
                                    let uu____2568 =
                                      let uu____2573 =
                                        FStar_Syntax_Syntax.mk_binder bv  in
                                      (uu____2573, b)  in
                                    ret uu____2568)
                             else fail "intro_rec: unification failed")))
        | FStar_Pervasives_Native.None  ->
            let uu____2587 =
              tts goal.FStar_Tactics_Types.context
                goal.FStar_Tactics_Types.goal_ty
               in
            fail1 "intro_rec: goal is not an arrow (%s)" uu____2587))
  
let (norm : FStar_Syntax_Embeddings.norm_step Prims.list -> Prims.unit tac) =
  fun s  ->
    bind cur_goal
      (fun goal  ->
         mlog
           (fun uu____2607  ->
              let uu____2608 =
                FStar_Syntax_Print.term_to_string
                  goal.FStar_Tactics_Types.witness
                 in
              FStar_Util.print1 "norm: witness = %s\n" uu____2608)
           (fun uu____2613  ->
              let steps =
                let uu____2617 = FStar_TypeChecker_Normalize.tr_norm_steps s
                   in
                FStar_List.append
                  [FStar_TypeChecker_Normalize.Reify;
                  FStar_TypeChecker_Normalize.UnfoldTac] uu____2617
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
                (let uu___91_2624 = goal  in
                 {
                   FStar_Tactics_Types.context =
                     (uu___91_2624.FStar_Tactics_Types.context);
                   FStar_Tactics_Types.witness = w;
                   FStar_Tactics_Types.goal_ty = t;
                   FStar_Tactics_Types.opts =
                     (uu___91_2624.FStar_Tactics_Types.opts);
                   FStar_Tactics_Types.is_guard =
                     (uu___91_2624.FStar_Tactics_Types.is_guard)
                 })))
  
let (norm_term_env :
  env ->
    FStar_Syntax_Embeddings.norm_step Prims.list ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac)
  =
  fun e  ->
    fun s  ->
      fun t  ->
        let uu____2642 =
          mlog
            (fun uu____2647  ->
               let uu____2648 = FStar_Syntax_Print.term_to_string t  in
               FStar_Util.print1 "norm_term: tm = %s\n" uu____2648)
            (fun uu____2650  ->
               bind get
                 (fun ps  ->
                    let opts =
                      match ps.FStar_Tactics_Types.goals with
                      | g::uu____2656 -> g.FStar_Tactics_Types.opts
                      | uu____2659 -> FStar_Options.peek ()  in
                    mlog
                      (fun uu____2664  ->
                         let uu____2665 =
                           tts ps.FStar_Tactics_Types.main_context t  in
                         FStar_Util.print1 "norm_term_env: t = %s\n"
                           uu____2665)
                      (fun uu____2668  ->
                         let uu____2669 = __tc e t  in
                         bind uu____2669
                           (fun uu____2690  ->
                              match uu____2690 with
                              | (t1,uu____2700,uu____2701) ->
                                  let steps =
                                    let uu____2705 =
                                      FStar_TypeChecker_Normalize.tr_norm_steps
                                        s
                                       in
                                    FStar_List.append
                                      [FStar_TypeChecker_Normalize.Reify;
                                      FStar_TypeChecker_Normalize.UnfoldTac]
                                      uu____2705
                                     in
                                  let t2 =
                                    normalize steps
                                      ps.FStar_Tactics_Types.main_context t1
                                     in
                                  ret t2))))
           in
        FStar_All.pipe_left (wrap_err "norm_term") uu____2642
  
let (refine_intro : Prims.unit tac) =
  let uu____2717 =
    bind cur_goal
      (fun g  ->
         let uu____2724 =
           FStar_TypeChecker_Rel.base_and_refinement
             g.FStar_Tactics_Types.context g.FStar_Tactics_Types.goal_ty
            in
         match uu____2724 with
         | (uu____2737,FStar_Pervasives_Native.None ) ->
             fail "not a refinement"
         | (t,FStar_Pervasives_Native.Some (bv,phi)) ->
             let g1 =
               let uu___92_2762 = g  in
               {
                 FStar_Tactics_Types.context =
                   (uu___92_2762.FStar_Tactics_Types.context);
                 FStar_Tactics_Types.witness =
                   (uu___92_2762.FStar_Tactics_Types.witness);
                 FStar_Tactics_Types.goal_ty = t;
                 FStar_Tactics_Types.opts =
                   (uu___92_2762.FStar_Tactics_Types.opts);
                 FStar_Tactics_Types.is_guard =
                   (uu___92_2762.FStar_Tactics_Types.is_guard)
               }  in
             let uu____2763 =
               let uu____2768 =
                 let uu____2773 =
                   let uu____2774 = FStar_Syntax_Syntax.mk_binder bv  in
                   [uu____2774]  in
                 FStar_Syntax_Subst.open_term uu____2773 phi  in
               match uu____2768 with
               | (bvs,phi1) ->
                   let uu____2781 =
                     let uu____2782 = FStar_List.hd bvs  in
                     FStar_Pervasives_Native.fst uu____2782  in
                   (uu____2781, phi1)
                in
             (match uu____2763 with
              | (bv1,phi1) ->
                  let uu____2795 =
                    let uu____2798 =
                      FStar_Syntax_Subst.subst
                        [FStar_Syntax_Syntax.NT
                           (bv1, (g.FStar_Tactics_Types.witness))] phi1
                       in
                    mk_irrelevant_goal "refine_intro refinement"
                      g.FStar_Tactics_Types.context uu____2798
                      g.FStar_Tactics_Types.opts
                     in
                  bind uu____2795
                    (fun g2  ->
                       bind __dismiss (fun uu____2802  -> add_goals [g1; g2]))))
     in
  FStar_All.pipe_left (wrap_err "refine_intro") uu____2717 
let (__exact_now : Prims.bool -> FStar_Syntax_Syntax.term -> Prims.unit tac)
  =
  fun set_expected_typ1  ->
    fun t  ->
      bind cur_goal
        (fun goal  ->
           let env =
             if set_expected_typ1
             then
               FStar_TypeChecker_Env.set_expected_typ
                 goal.FStar_Tactics_Types.context
                 goal.FStar_Tactics_Types.goal_ty
             else goal.FStar_Tactics_Types.context  in
           let uu____2823 = __tc env t  in
           bind uu____2823
             (fun uu____2842  ->
                match uu____2842 with
                | (t1,typ,guard) ->
                    mlog
                      (fun uu____2857  ->
                         let uu____2858 =
                           tts goal.FStar_Tactics_Types.context typ  in
                         let uu____2859 =
                           FStar_TypeChecker_Rel.guard_to_string
                             goal.FStar_Tactics_Types.context guard
                            in
                         FStar_Util.print2
                           "__exact_now: got type %s\n__exact_now and guard %s\n"
                           uu____2858 uu____2859)
                      (fun uu____2862  ->
                         let uu____2863 =
                           proc_guard "__exact typing"
                             goal.FStar_Tactics_Types.context guard
                             goal.FStar_Tactics_Types.opts
                            in
                         bind uu____2863
                           (fun uu____2867  ->
                              mlog
                                (fun uu____2871  ->
                                   let uu____2872 =
                                     tts goal.FStar_Tactics_Types.context typ
                                      in
                                   let uu____2873 =
                                     tts goal.FStar_Tactics_Types.context
                                       goal.FStar_Tactics_Types.goal_ty
                                      in
                                   FStar_Util.print2
                                     "__exact_now: unifying %s and %s\n"
                                     uu____2872 uu____2873)
                                (fun uu____2876  ->
                                   let uu____2877 =
                                     do_unify
                                       goal.FStar_Tactics_Types.context typ
                                       goal.FStar_Tactics_Types.goal_ty
                                      in
                                   bind uu____2877
                                     (fun b  ->
                                        if b
                                        then solve goal t1
                                        else
                                          (let uu____2885 =
                                             tts
                                               goal.FStar_Tactics_Types.context
                                               t1
                                              in
                                           let uu____2886 =
                                             tts
                                               goal.FStar_Tactics_Types.context
                                               typ
                                              in
                                           let uu____2887 =
                                             tts
                                               goal.FStar_Tactics_Types.context
                                               goal.FStar_Tactics_Types.goal_ty
                                              in
                                           let uu____2888 =
                                             tts
                                               goal.FStar_Tactics_Types.context
                                               goal.FStar_Tactics_Types.witness
                                              in
                                           fail4
                                             "%s : %s does not exactly solve the goal %s (witness = %s)"
                                             uu____2885 uu____2886 uu____2887
                                             uu____2888)))))))
  
let (t_exact : Prims.bool -> FStar_Syntax_Syntax.term -> Prims.unit tac) =
  fun set_expected_typ1  ->
    fun tm  ->
      let uu____2899 =
        mlog
          (fun uu____2904  ->
             let uu____2905 = FStar_Syntax_Print.term_to_string tm  in
             FStar_Util.print1 "t_exact: tm = %s\n" uu____2905)
          (fun uu____2908  ->
             let uu____2909 =
               let uu____2916 = __exact_now set_expected_typ1 tm  in
               trytac' uu____2916  in
             bind uu____2909
               (fun uu___58_2925  ->
                  match uu___58_2925 with
                  | FStar_Util.Inr r -> ret ()
                  | FStar_Util.Inl e ->
                      let uu____2934 =
                        let uu____2941 =
                          let uu____2944 =
                            norm [FStar_Syntax_Embeddings.Delta]  in
                          bind uu____2944
                            (fun uu____2948  ->
                               bind refine_intro
                                 (fun uu____2950  ->
                                    __exact_now set_expected_typ1 tm))
                           in
                        trytac' uu____2941  in
                      bind uu____2934
                        (fun uu___57_2957  ->
                           match uu___57_2957 with
                           | FStar_Util.Inr r -> ret ()
                           | FStar_Util.Inl uu____2965 -> fail e)))
         in
      FStar_All.pipe_left (wrap_err "exact") uu____2899
  
let (uvar_free_in_goal :
  FStar_Syntax_Syntax.uvar -> FStar_Tactics_Types.goal -> Prims.bool) =
  fun u  ->
    fun g  ->
      if g.FStar_Tactics_Types.is_guard
      then false
      else
        (let free_uvars =
           let uu____2980 =
             let uu____2987 =
               FStar_Syntax_Free.uvars g.FStar_Tactics_Types.goal_ty  in
             FStar_Util.set_elements uu____2987  in
           FStar_List.map FStar_Pervasives_Native.fst uu____2980  in
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
          let uu____3047 = f x  in
          bind uu____3047
            (fun y  ->
               let uu____3055 = mapM f xs  in
               bind uu____3055 (fun ys  -> ret (y :: ys)))
  
exception NoUnif 
let (uu___is_NoUnif : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with | NoUnif  -> true | uu____3073 -> false
  
let rec (__apply :
  Prims.bool ->
    FStar_Syntax_Syntax.term -> FStar_Reflection_Data.typ -> Prims.unit tac)
  =
  fun uopt  ->
    fun tm  ->
      fun typ  ->
        bind cur_goal
          (fun goal  ->
             mlog
               (fun uu____3091  ->
                  let uu____3092 = FStar_Syntax_Print.term_to_string tm  in
                  FStar_Util.print1 ">>> Calling __exact(%s)\n" uu____3092)
               (fun uu____3095  ->
                  let uu____3096 =
                    let uu____3101 =
                      let uu____3104 = t_exact false tm  in
                      with_policy FStar_Tactics_Types.Force uu____3104  in
                    trytac_exn uu____3101  in
                  bind uu____3096
                    (fun uu___59_3111  ->
                       match uu___59_3111 with
                       | FStar_Pervasives_Native.Some r -> ret ()
                       | FStar_Pervasives_Native.None  ->
                           mlog
                             (fun uu____3119  ->
                                let uu____3120 =
                                  FStar_Syntax_Print.term_to_string typ  in
                                FStar_Util.print1 ">>> typ = %s\n" uu____3120)
                             (fun uu____3123  ->
                                let uu____3124 =
                                  FStar_Syntax_Util.arrow_one typ  in
                                match uu____3124 with
                                | FStar_Pervasives_Native.None  ->
                                    FStar_Exn.raise NoUnif
                                | FStar_Pervasives_Native.Some ((bv,aq),c) ->
                                    mlog
                                      (fun uu____3156  ->
                                         let uu____3157 =
                                           FStar_Syntax_Print.binder_to_string
                                             (bv, aq)
                                            in
                                         FStar_Util.print1
                                           "__apply: pushing binder %s\n"
                                           uu____3157)
                                      (fun uu____3160  ->
                                         let uu____3161 =
                                           let uu____3162 =
                                             FStar_Syntax_Util.is_total_comp
                                               c
                                              in
                                           Prims.op_Negation uu____3162  in
                                         if uu____3161
                                         then
                                           fail "apply: not total codomain"
                                         else
                                           (let uu____3166 =
                                              new_uvar "apply"
                                                goal.FStar_Tactics_Types.context
                                                bv.FStar_Syntax_Syntax.sort
                                               in
                                            bind uu____3166
                                              (fun u  ->
                                                 let tm' =
                                                   FStar_Syntax_Syntax.mk_Tm_app
                                                     tm [(u, aq)]
                                                     FStar_Pervasives_Native.None
                                                     tm.FStar_Syntax_Syntax.pos
                                                    in
                                                 let typ' =
                                                   let uu____3186 =
                                                     comp_to_typ c  in
                                                   FStar_All.pipe_left
                                                     (FStar_Syntax_Subst.subst
                                                        [FStar_Syntax_Syntax.NT
                                                           (bv, u)])
                                                     uu____3186
                                                    in
                                                 let uu____3187 =
                                                   __apply uopt tm' typ'  in
                                                 bind uu____3187
                                                   (fun uu____3195  ->
                                                      let u1 =
                                                        bnorm
                                                          goal.FStar_Tactics_Types.context
                                                          u
                                                         in
                                                      let uu____3197 =
                                                        let uu____3198 =
                                                          let uu____3201 =
                                                            let uu____3202 =
                                                              FStar_Syntax_Util.head_and_args
                                                                u1
                                                               in
                                                            FStar_Pervasives_Native.fst
                                                              uu____3202
                                                             in
                                                          FStar_Syntax_Subst.compress
                                                            uu____3201
                                                           in
                                                        uu____3198.FStar_Syntax_Syntax.n
                                                         in
                                                      match uu____3197 with
                                                      | FStar_Syntax_Syntax.Tm_uvar
                                                          (uvar,uu____3230)
                                                          ->
                                                          bind get
                                                            (fun ps  ->
                                                               let uu____3258
                                                                 =
                                                                 uopt &&
                                                                   (uvar_free
                                                                    uvar ps)
                                                                  in
                                                               if uu____3258
                                                               then ret ()
                                                               else
                                                                 (let uu____3262
                                                                    =
                                                                    let uu____3265
                                                                    =
                                                                    let uu___93_3266
                                                                    = goal
                                                                     in
                                                                    let uu____3267
                                                                    =
                                                                    bnorm
                                                                    goal.FStar_Tactics_Types.context
                                                                    u1  in
                                                                    let uu____3268
                                                                    =
                                                                    bnorm
                                                                    goal.FStar_Tactics_Types.context
                                                                    bv.FStar_Syntax_Syntax.sort
                                                                     in
                                                                    {
                                                                    FStar_Tactics_Types.context
                                                                    =
                                                                    (uu___93_3266.FStar_Tactics_Types.context);
                                                                    FStar_Tactics_Types.witness
                                                                    =
                                                                    uu____3267;
                                                                    FStar_Tactics_Types.goal_ty
                                                                    =
                                                                    uu____3268;
                                                                    FStar_Tactics_Types.opts
                                                                    =
                                                                    (uu___93_3266.FStar_Tactics_Types.opts);
                                                                    FStar_Tactics_Types.is_guard
                                                                    = false
                                                                    }  in
                                                                    [uu____3265]
                                                                     in
                                                                  add_goals
                                                                    uu____3262))
                                                      | t -> ret ()))))))))
  
let try_unif : 'a . 'a tac -> 'a tac -> 'a tac =
  fun t  ->
    fun t'  -> mk_tac (fun ps  -> try run t ps with | NoUnif  -> run t' ps)
  
let (apply : Prims.bool -> FStar_Syntax_Syntax.term -> Prims.unit tac) =
  fun uopt  ->
    fun tm  ->
      let uu____3314 =
        mlog
          (fun uu____3319  ->
             let uu____3320 = FStar_Syntax_Print.term_to_string tm  in
             FStar_Util.print1 "apply: tm = %s\n" uu____3320)
          (fun uu____3322  ->
             bind cur_goal
               (fun goal  ->
                  let uu____3326 = __tc goal.FStar_Tactics_Types.context tm
                     in
                  bind uu____3326
                    (fun uu____3348  ->
                       match uu____3348 with
                       | (tm1,typ,guard) ->
                           let typ1 =
                             bnorm goal.FStar_Tactics_Types.context typ  in
                           let uu____3361 =
                             let uu____3364 =
                               let uu____3367 = __apply uopt tm1 typ1  in
                               bind uu____3367
                                 (fun uu____3371  ->
                                    proc_guard "apply guard"
                                      goal.FStar_Tactics_Types.context guard
                                      goal.FStar_Tactics_Types.opts)
                                in
                             focus uu____3364  in
                           let uu____3372 =
                             let uu____3375 =
                               tts goal.FStar_Tactics_Types.context tm1  in
                             let uu____3376 =
                               tts goal.FStar_Tactics_Types.context typ1  in
                             let uu____3377 =
                               tts goal.FStar_Tactics_Types.context
                                 goal.FStar_Tactics_Types.goal_ty
                                in
                             fail3
                               "Cannot instantiate %s (of type %s) to match goal (%s)"
                               uu____3375 uu____3376 uu____3377
                              in
                           try_unif uu____3361 uu____3372)))
         in
      FStar_All.pipe_left (wrap_err "apply") uu____3314
  
let (lemma_or_sq :
  FStar_Syntax_Syntax.comp ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun c  ->
    let ct = FStar_Syntax_Util.comp_to_comp_typ_nouniv c  in
    if
      FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
        FStar_Parser_Const.effect_Lemma_lid
    then
      let uu____3404 =
        match ct.FStar_Syntax_Syntax.effect_args with
        | pre::post::uu____3423 ->
            ((FStar_Pervasives_Native.fst pre),
              (FStar_Pervasives_Native.fst post))
        | uu____3464 -> failwith "apply_lemma: impossible: not a lemma"  in
      match uu____3404 with
      | (pre,post) ->
          let post1 =
            let uu____3500 =
              let uu____3509 =
                FStar_Syntax_Syntax.as_arg FStar_Syntax_Util.exp_unit  in
              [uu____3509]  in
            FStar_Syntax_Util.mk_app post uu____3500  in
          FStar_Pervasives_Native.Some (pre, post1)
    else
      if FStar_Syntax_Util.is_pure_effect ct.FStar_Syntax_Syntax.effect_name
      then
        (let uu____3529 =
           FStar_Syntax_Util.un_squash ct.FStar_Syntax_Syntax.result_typ  in
         FStar_Util.map_opt uu____3529
           (fun post  -> (FStar_Syntax_Util.t_true, post)))
      else FStar_Pervasives_Native.None
  
let (apply_lemma : FStar_Syntax_Syntax.term -> Prims.unit tac) =
  fun tm  ->
    let uu____3560 =
      let uu____3563 =
        mlog
          (fun uu____3568  ->
             let uu____3569 = FStar_Syntax_Print.term_to_string tm  in
             FStar_Util.print1 "apply_lemma: tm = %s\n" uu____3569)
          (fun uu____3572  ->
             let is_unit_t t =
               let uu____3577 =
                 let uu____3578 = FStar_Syntax_Subst.compress t  in
                 uu____3578.FStar_Syntax_Syntax.n  in
               match uu____3577 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.unit_lid
                   -> true
               | uu____3582 -> false  in
             bind cur_goal
               (fun goal  ->
                  let uu____3586 = __tc goal.FStar_Tactics_Types.context tm
                     in
                  bind uu____3586
                    (fun uu____3609  ->
                       match uu____3609 with
                       | (tm1,t,guard) ->
                           let uu____3621 =
                             FStar_Syntax_Util.arrow_formals_comp t  in
                           (match uu____3621 with
                            | (bs,comp) ->
                                let uu____3648 = lemma_or_sq comp  in
                                (match uu____3648 with
                                 | FStar_Pervasives_Native.None  ->
                                     fail "not a lemma or squashed function"
                                 | FStar_Pervasives_Native.Some (pre,post) ->
                                     let uu____3667 =
                                       FStar_List.fold_left
                                         (fun uu____3713  ->
                                            fun uu____3714  ->
                                              match (uu____3713, uu____3714)
                                              with
                                              | ((uvs,guard1,subst1),(b,aq))
                                                  ->
                                                  let b_t =
                                                    FStar_Syntax_Subst.subst
                                                      subst1
                                                      b.FStar_Syntax_Syntax.sort
                                                     in
                                                  let uu____3817 =
                                                    is_unit_t b_t  in
                                                  if uu____3817
                                                  then
                                                    (((FStar_Syntax_Util.exp_unit,
                                                        aq) :: uvs), guard1,
                                                      ((FStar_Syntax_Syntax.NT
                                                          (b,
                                                            FStar_Syntax_Util.exp_unit))
                                                      :: subst1))
                                                  else
                                                    (let uu____3855 =
                                                       FStar_TypeChecker_Util.new_implicit_var
                                                         "apply_lemma"
                                                         (goal.FStar_Tactics_Types.goal_ty).FStar_Syntax_Syntax.pos
                                                         goal.FStar_Tactics_Types.context
                                                         b_t
                                                        in
                                                     match uu____3855 with
                                                     | (u,uu____3885,g_u) ->
                                                         let uu____3899 =
                                                           FStar_TypeChecker_Rel.conj_guard
                                                             guard1 g_u
                                                            in
                                                         (((u, aq) :: uvs),
                                                           uu____3899,
                                                           ((FStar_Syntax_Syntax.NT
                                                               (b, u)) ::
                                                           subst1))))
                                         ([], guard, []) bs
                                        in
                                     (match uu____3667 with
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
                                          let uu____3970 =
                                            let uu____3973 =
                                              FStar_Syntax_Util.mk_squash
                                                FStar_Syntax_Syntax.U_zero
                                                post1
                                               in
                                            do_unify
                                              goal.FStar_Tactics_Types.context
                                              uu____3973
                                              goal.FStar_Tactics_Types.goal_ty
                                             in
                                          bind uu____3970
                                            (fun b  ->
                                               if Prims.op_Negation b
                                               then
                                                 let uu____3981 =
                                                   tts
                                                     goal.FStar_Tactics_Types.context
                                                     tm1
                                                    in
                                                 let uu____3982 =
                                                   let uu____3983 =
                                                     FStar_Syntax_Util.mk_squash
                                                       FStar_Syntax_Syntax.U_zero
                                                       post1
                                                      in
                                                   tts
                                                     goal.FStar_Tactics_Types.context
                                                     uu____3983
                                                    in
                                                 let uu____3984 =
                                                   tts
                                                     goal.FStar_Tactics_Types.context
                                                     goal.FStar_Tactics_Types.goal_ty
                                                    in
                                                 fail3
                                                   "Cannot instantiate lemma %s (with postcondition: %s) to match goal (%s)"
                                                   uu____3981 uu____3982
                                                   uu____3984
                                               else
                                                 (let uu____3986 =
                                                    add_implicits
                                                      implicits.FStar_TypeChecker_Env.implicits
                                                     in
                                                  bind uu____3986
                                                    (fun uu____3991  ->
                                                       let uu____3992 =
                                                         solve goal
                                                           FStar_Syntax_Util.exp_unit
                                                          in
                                                       bind uu____3992
                                                         (fun uu____4000  ->
                                                            let is_free_uvar
                                                              uv t1 =
                                                              let free_uvars
                                                                =
                                                                let uu____4011
                                                                  =
                                                                  let uu____4018
                                                                    =
                                                                    FStar_Syntax_Free.uvars
                                                                    t1  in
                                                                  FStar_Util.set_elements
                                                                    uu____4018
                                                                   in
                                                                FStar_List.map
                                                                  FStar_Pervasives_Native.fst
                                                                  uu____4011
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
                                                              let uu____4059
                                                                =
                                                                FStar_Syntax_Util.head_and_args
                                                                  t1
                                                                 in
                                                              match uu____4059
                                                              with
                                                              | (hd1,uu____4075)
                                                                  ->
                                                                  (match 
                                                                    hd1.FStar_Syntax_Syntax.n
                                                                   with
                                                                   | 
                                                                   FStar_Syntax_Syntax.Tm_uvar
                                                                    (uv,uu____4097)
                                                                    ->
                                                                    appears
                                                                    uv goals
                                                                   | 
                                                                   uu____4122
                                                                    -> false)
                                                               in
                                                            let uu____4123 =
                                                              FStar_All.pipe_right
                                                                implicits.FStar_TypeChecker_Env.implicits
                                                                (mapM
                                                                   (fun
                                                                    uu____4195
                                                                     ->
                                                                    match uu____4195
                                                                    with
                                                                    | 
                                                                    (_msg,env,_uvar,term,typ,uu____4223)
                                                                    ->
                                                                    let uu____4224
                                                                    =
                                                                    FStar_Syntax_Util.head_and_args
                                                                    term  in
                                                                    (match uu____4224
                                                                    with
                                                                    | 
                                                                    (hd1,uu____4250)
                                                                    ->
                                                                    let uu____4271
                                                                    =
                                                                    let uu____4272
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    hd1  in
                                                                    uu____4272.FStar_Syntax_Syntax.n
                                                                     in
                                                                    (match uu____4271
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Tm_uvar
                                                                    uu____4285
                                                                    ->
                                                                    let uu____4302
                                                                    =
                                                                    let uu____4311
                                                                    =
                                                                    let uu____4314
                                                                    =
                                                                    let uu___96_4315
                                                                    = goal
                                                                     in
                                                                    let uu____4316
                                                                    =
                                                                    bnorm
                                                                    goal.FStar_Tactics_Types.context
                                                                    term  in
                                                                    let uu____4317
                                                                    =
                                                                    bnorm
                                                                    goal.FStar_Tactics_Types.context
                                                                    typ  in
                                                                    {
                                                                    FStar_Tactics_Types.context
                                                                    =
                                                                    (uu___96_4315.FStar_Tactics_Types.context);
                                                                    FStar_Tactics_Types.witness
                                                                    =
                                                                    uu____4316;
                                                                    FStar_Tactics_Types.goal_ty
                                                                    =
                                                                    uu____4317;
                                                                    FStar_Tactics_Types.opts
                                                                    =
                                                                    (uu___96_4315.FStar_Tactics_Types.opts);
                                                                    FStar_Tactics_Types.is_guard
                                                                    =
                                                                    (uu___96_4315.FStar_Tactics_Types.is_guard)
                                                                    }  in
                                                                    [uu____4314]
                                                                     in
                                                                    (uu____4311,
                                                                    [])  in
                                                                    ret
                                                                    uu____4302
                                                                    | 
                                                                    uu____4330
                                                                    ->
                                                                    let g_typ
                                                                    =
                                                                    let uu____4332
                                                                    =
                                                                    FStar_Options.__temp_fast_implicits
                                                                    ()  in
                                                                    if
                                                                    uu____4332
                                                                    then
                                                                    FStar_TypeChecker_TcTerm.check_type_of_well_typed_term
                                                                    false env
                                                                    term typ
                                                                    else
                                                                    (let term1
                                                                    =
                                                                    bnorm env
                                                                    term  in
                                                                    let uu____4335
                                                                    =
                                                                    let uu____4342
                                                                    =
                                                                    FStar_TypeChecker_Env.set_expected_typ
                                                                    env typ
                                                                     in
                                                                    env.FStar_TypeChecker_Env.type_of
                                                                    uu____4342
                                                                    term1  in
                                                                    match uu____4335
                                                                    with
                                                                    | 
                                                                    (uu____4343,uu____4344,g_typ)
                                                                    -> g_typ)
                                                                     in
                                                                    let uu____4346
                                                                    =
                                                                    goal_from_guard
                                                                    "apply_lemma solved arg"
                                                                    goal.FStar_Tactics_Types.context
                                                                    g_typ
                                                                    goal.FStar_Tactics_Types.opts
                                                                     in
                                                                    bind
                                                                    uu____4346
                                                                    (fun
                                                                    uu___60_4362
                                                                     ->
                                                                    match uu___60_4362
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
                                                            bind uu____4123
                                                              (fun goals_  ->
                                                                 let sub_goals
                                                                   =
                                                                   let uu____4430
                                                                    =
                                                                    FStar_List.map
                                                                    FStar_Pervasives_Native.fst
                                                                    goals_
                                                                     in
                                                                   FStar_List.flatten
                                                                    uu____4430
                                                                    in
                                                                 let smt_goals
                                                                   =
                                                                   let uu____4452
                                                                    =
                                                                    FStar_List.map
                                                                    FStar_Pervasives_Native.snd
                                                                    goals_
                                                                     in
                                                                   FStar_List.flatten
                                                                    uu____4452
                                                                    in
                                                                 let rec filter'
                                                                   a f xs =
                                                                   match xs
                                                                   with
                                                                   | 
                                                                   [] -> []
                                                                   | 
                                                                   x::xs1 ->
                                                                    let uu____4507
                                                                    = f x xs1
                                                                     in
                                                                    if
                                                                    uu____4507
                                                                    then
                                                                    let uu____4510
                                                                    =
                                                                    filter'
                                                                    () f xs1
                                                                     in x ::
                                                                    uu____4510
                                                                    else
                                                                    filter'
                                                                    () f xs1
                                                                    in
                                                                 let sub_goals1
                                                                   =
                                                                   Obj.magic
                                                                    (filter'
                                                                    ()
                                                                    (fun a438
                                                                     ->
                                                                    fun a439 
                                                                    ->
                                                                    (Obj.magic
                                                                    (fun g 
                                                                    ->
                                                                    fun goals
                                                                     ->
                                                                    let uu____4524
                                                                    =
                                                                    checkone
                                                                    g.FStar_Tactics_Types.witness
                                                                    goals  in
                                                                    Prims.op_Negation
                                                                    uu____4524))
                                                                    a438 a439)
                                                                    (Obj.magic
                                                                    sub_goals))
                                                                    in
                                                                 let uu____4525
                                                                   =
                                                                   proc_guard
                                                                    "apply_lemma guard"
                                                                    goal.FStar_Tactics_Types.context
                                                                    guard
                                                                    goal.FStar_Tactics_Types.opts
                                                                    in
                                                                 bind
                                                                   uu____4525
                                                                   (fun
                                                                    uu____4530
                                                                     ->
                                                                    let uu____4531
                                                                    =
                                                                    let uu____4534
                                                                    =
                                                                    let uu____4535
                                                                    =
                                                                    let uu____4536
                                                                    =
                                                                    FStar_Syntax_Util.mk_squash
                                                                    FStar_Syntax_Syntax.U_zero
                                                                    pre1  in
                                                                    istrivial
                                                                    goal.FStar_Tactics_Types.context
                                                                    uu____4536
                                                                     in
                                                                    Prims.op_Negation
                                                                    uu____4535
                                                                     in
                                                                    if
                                                                    uu____4534
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
                                                                    uu____4531
                                                                    (fun
                                                                    uu____4542
                                                                     ->
                                                                    let uu____4543
                                                                    =
                                                                    add_smt_goals
                                                                    smt_goals
                                                                     in
                                                                    bind
                                                                    uu____4543
                                                                    (fun
                                                                    uu____4547
                                                                     ->
                                                                    add_goals
                                                                    sub_goals1))))))))))))))
         in
      focus uu____3563  in
    FStar_All.pipe_left (wrap_err "apply_lemma") uu____3560
  
let (destruct_eq' :
  FStar_Reflection_Data.typ ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun typ  ->
    let uu____4567 = FStar_Syntax_Util.destruct_typ_as_formula typ  in
    match uu____4567 with
    | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn
        (l,uu____4577::(e1,uu____4579)::(e2,uu____4581)::[])) when
        FStar_Ident.lid_equals l FStar_Parser_Const.eq2_lid ->
        FStar_Pervasives_Native.Some (e1, e2)
    | uu____4640 -> FStar_Pervasives_Native.None
  
let (destruct_eq :
  FStar_Reflection_Data.typ ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun typ  ->
    let uu____4662 = destruct_eq' typ  in
    match uu____4662 with
    | FStar_Pervasives_Native.Some t -> FStar_Pervasives_Native.Some t
    | FStar_Pervasives_Native.None  ->
        let uu____4692 = FStar_Syntax_Util.un_squash typ  in
        (match uu____4692 with
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
        let uu____4748 = FStar_TypeChecker_Env.pop_bv e1  in
        match uu____4748 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (bv',e') ->
            if FStar_Syntax_Syntax.bv_eq bvar bv'
            then FStar_Pervasives_Native.Some (e', [])
            else
              (let uu____4796 = aux e'  in
               FStar_Util.map_opt uu____4796
                 (fun uu____4820  ->
                    match uu____4820 with | (e'',bvs) -> (e'', (bv' :: bvs))))
         in
      let uu____4841 = aux e  in
      FStar_Util.map_opt uu____4841
        (fun uu____4865  ->
           match uu____4865 with | (e',bvs) -> (e', (FStar_List.rev bvs)))
  
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
          let uu____4920 = split_env b1 g.FStar_Tactics_Types.context  in
          FStar_Util.map_opt uu____4920
            (fun uu____4944  ->
               match uu____4944 with
               | (e0,bvs) ->
                   let s1 bv =
                     let uu___97_4961 = bv  in
                     let uu____4962 =
                       FStar_Syntax_Subst.subst s bv.FStar_Syntax_Syntax.sort
                        in
                     {
                       FStar_Syntax_Syntax.ppname =
                         (uu___97_4961.FStar_Syntax_Syntax.ppname);
                       FStar_Syntax_Syntax.index =
                         (uu___97_4961.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort = uu____4962
                     }  in
                   let bvs1 = FStar_List.map s1 bvs  in
                   let c = push_bvs e0 (b2 :: bvs1)  in
                   let w =
                     FStar_Syntax_Subst.subst s g.FStar_Tactics_Types.witness
                      in
                   let t =
                     FStar_Syntax_Subst.subst s g.FStar_Tactics_Types.goal_ty
                      in
                   let uu___98_4971 = g  in
                   {
                     FStar_Tactics_Types.context = c;
                     FStar_Tactics_Types.witness = w;
                     FStar_Tactics_Types.goal_ty = t;
                     FStar_Tactics_Types.opts =
                       (uu___98_4971.FStar_Tactics_Types.opts);
                     FStar_Tactics_Types.is_guard =
                       (uu___98_4971.FStar_Tactics_Types.is_guard)
                   })
  
let (rewrite : FStar_Syntax_Syntax.binder -> Prims.unit tac) =
  fun h  ->
    bind cur_goal
      (fun goal  ->
         let uu____4984 = h  in
         match uu____4984 with
         | (bv,uu____4988) ->
             mlog
               (fun uu____4992  ->
                  let uu____4993 = FStar_Syntax_Print.bv_to_string bv  in
                  let uu____4994 =
                    tts goal.FStar_Tactics_Types.context
                      bv.FStar_Syntax_Syntax.sort
                     in
                  FStar_Util.print2 "+++Rewrite %s : %s\n" uu____4993
                    uu____4994)
               (fun uu____4997  ->
                  let uu____4998 =
                    split_env bv goal.FStar_Tactics_Types.context  in
                  match uu____4998 with
                  | FStar_Pervasives_Native.None  ->
                      fail "rewrite: binder not found in environment"
                  | FStar_Pervasives_Native.Some (e0,bvs) ->
                      let uu____5027 =
                        destruct_eq bv.FStar_Syntax_Syntax.sort  in
                      (match uu____5027 with
                       | FStar_Pervasives_Native.Some (x,e) ->
                           let uu____5042 =
                             let uu____5043 = FStar_Syntax_Subst.compress x
                                in
                             uu____5043.FStar_Syntax_Syntax.n  in
                           (match uu____5042 with
                            | FStar_Syntax_Syntax.Tm_name x1 ->
                                let s = [FStar_Syntax_Syntax.NT (x1, e)]  in
                                let s1 bv1 =
                                  let uu___99_5056 = bv1  in
                                  let uu____5057 =
                                    FStar_Syntax_Subst.subst s
                                      bv1.FStar_Syntax_Syntax.sort
                                     in
                                  {
                                    FStar_Syntax_Syntax.ppname =
                                      (uu___99_5056.FStar_Syntax_Syntax.ppname);
                                    FStar_Syntax_Syntax.index =
                                      (uu___99_5056.FStar_Syntax_Syntax.index);
                                    FStar_Syntax_Syntax.sort = uu____5057
                                  }  in
                                let bvs1 = FStar_List.map s1 bvs  in
                                let uu____5063 =
                                  let uu___100_5064 = goal  in
                                  let uu____5065 = push_bvs e0 (bv :: bvs1)
                                     in
                                  let uu____5066 =
                                    FStar_Syntax_Subst.subst s
                                      goal.FStar_Tactics_Types.witness
                                     in
                                  let uu____5067 =
                                    FStar_Syntax_Subst.subst s
                                      goal.FStar_Tactics_Types.goal_ty
                                     in
                                  {
                                    FStar_Tactics_Types.context = uu____5065;
                                    FStar_Tactics_Types.witness = uu____5066;
                                    FStar_Tactics_Types.goal_ty = uu____5067;
                                    FStar_Tactics_Types.opts =
                                      (uu___100_5064.FStar_Tactics_Types.opts);
                                    FStar_Tactics_Types.is_guard =
                                      (uu___100_5064.FStar_Tactics_Types.is_guard)
                                  }  in
                                replace_cur uu____5063
                            | uu____5068 ->
                                fail
                                  "rewrite: Not an equality hypothesis with a variable on the LHS")
                       | uu____5069 ->
                           fail "rewrite: Not an equality hypothesis")))
  
let (rename_to :
  FStar_Syntax_Syntax.binder -> Prims.string -> Prims.unit tac) =
  fun b  ->
    fun s  ->
      bind cur_goal
        (fun goal  ->
           let uu____5094 = b  in
           match uu____5094 with
           | (bv,uu____5098) ->
               let bv' =
                 FStar_Syntax_Syntax.freshen_bv
                   (let uu___101_5102 = bv  in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (FStar_Ident.mk_ident
                           (s,
                             ((bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange)));
                      FStar_Syntax_Syntax.index =
                        (uu___101_5102.FStar_Syntax_Syntax.index);
                      FStar_Syntax_Syntax.sort =
                        (uu___101_5102.FStar_Syntax_Syntax.sort)
                    })
                  in
               let s1 =
                 let uu____5106 =
                   let uu____5107 =
                     let uu____5114 = FStar_Syntax_Syntax.bv_to_name bv'  in
                     (bv, uu____5114)  in
                   FStar_Syntax_Syntax.NT uu____5107  in
                 [uu____5106]  in
               let uu____5115 = subst_goal bv bv' s1 goal  in
               (match uu____5115 with
                | FStar_Pervasives_Native.None  ->
                    fail "rename_to: binder not found in environment"
                | FStar_Pervasives_Native.Some goal1 -> replace_cur goal1))
  
let (binder_retype : FStar_Syntax_Syntax.binder -> Prims.unit tac) =
  fun b  ->
    bind cur_goal
      (fun goal  ->
         let uu____5134 = b  in
         match uu____5134 with
         | (bv,uu____5138) ->
             let uu____5139 = split_env bv goal.FStar_Tactics_Types.context
                in
             (match uu____5139 with
              | FStar_Pervasives_Native.None  ->
                  fail "binder_retype: binder is not present in environment"
              | FStar_Pervasives_Native.Some (e0,bvs) ->
                  let uu____5168 = FStar_Syntax_Util.type_u ()  in
                  (match uu____5168 with
                   | (ty,u) ->
                       let uu____5177 = new_uvar "binder_retype" e0 ty  in
                       bind uu____5177
                         (fun t'  ->
                            let bv'' =
                              let uu___102_5187 = bv  in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___102_5187.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___102_5187.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = t'
                              }  in
                            let s =
                              let uu____5191 =
                                let uu____5192 =
                                  let uu____5199 =
                                    FStar_Syntax_Syntax.bv_to_name bv''  in
                                  (bv, uu____5199)  in
                                FStar_Syntax_Syntax.NT uu____5192  in
                              [uu____5191]  in
                            let bvs1 =
                              FStar_List.map
                                (fun b1  ->
                                   let uu___103_5207 = b1  in
                                   let uu____5208 =
                                     FStar_Syntax_Subst.subst s
                                       b1.FStar_Syntax_Syntax.sort
                                      in
                                   {
                                     FStar_Syntax_Syntax.ppname =
                                       (uu___103_5207.FStar_Syntax_Syntax.ppname);
                                     FStar_Syntax_Syntax.index =
                                       (uu___103_5207.FStar_Syntax_Syntax.index);
                                     FStar_Syntax_Syntax.sort = uu____5208
                                   }) bvs
                               in
                            let env' = push_bvs e0 (bv'' :: bvs1)  in
                            bind __dismiss
                              (fun uu____5214  ->
                                 let uu____5215 =
                                   let uu____5218 =
                                     let uu____5221 =
                                       let uu___104_5222 = goal  in
                                       let uu____5223 =
                                         FStar_Syntax_Subst.subst s
                                           goal.FStar_Tactics_Types.witness
                                          in
                                       let uu____5224 =
                                         FStar_Syntax_Subst.subst s
                                           goal.FStar_Tactics_Types.goal_ty
                                          in
                                       {
                                         FStar_Tactics_Types.context = env';
                                         FStar_Tactics_Types.witness =
                                           uu____5223;
                                         FStar_Tactics_Types.goal_ty =
                                           uu____5224;
                                         FStar_Tactics_Types.opts =
                                           (uu___104_5222.FStar_Tactics_Types.opts);
                                         FStar_Tactics_Types.is_guard =
                                           (uu___104_5222.FStar_Tactics_Types.is_guard)
                                       }  in
                                     [uu____5221]  in
                                   add_goals uu____5218  in
                                 bind uu____5215
                                   (fun uu____5227  ->
                                      let uu____5228 =
                                        FStar_Syntax_Util.mk_eq2
                                          (FStar_Syntax_Syntax.U_succ u) ty
                                          bv.FStar_Syntax_Syntax.sort t'
                                         in
                                      add_irrelevant_goal
                                        "binder_retype equation" e0
                                        uu____5228
                                        goal.FStar_Tactics_Types.opts))))))
  
let (norm_binder_type :
  FStar_Syntax_Embeddings.norm_step Prims.list ->
    FStar_Syntax_Syntax.binder -> Prims.unit tac)
  =
  fun s  ->
    fun b  ->
      bind cur_goal
        (fun goal  ->
           let uu____5249 = b  in
           match uu____5249 with
           | (bv,uu____5253) ->
               let uu____5254 = split_env bv goal.FStar_Tactics_Types.context
                  in
               (match uu____5254 with
                | FStar_Pervasives_Native.None  ->
                    fail
                      "binder_retype: binder is not present in environment"
                | FStar_Pervasives_Native.Some (e0,bvs) ->
                    let steps =
                      let uu____5286 =
                        FStar_TypeChecker_Normalize.tr_norm_steps s  in
                      FStar_List.append
                        [FStar_TypeChecker_Normalize.Reify;
                        FStar_TypeChecker_Normalize.UnfoldTac] uu____5286
                       in
                    let sort' =
                      normalize steps e0 bv.FStar_Syntax_Syntax.sort  in
                    let bv' =
                      let uu___105_5291 = bv  in
                      {
                        FStar_Syntax_Syntax.ppname =
                          (uu___105_5291.FStar_Syntax_Syntax.ppname);
                        FStar_Syntax_Syntax.index =
                          (uu___105_5291.FStar_Syntax_Syntax.index);
                        FStar_Syntax_Syntax.sort = sort'
                      }  in
                    let env' = push_bvs e0 (bv' :: bvs)  in
                    replace_cur
                      (let uu___106_5295 = goal  in
                       {
                         FStar_Tactics_Types.context = env';
                         FStar_Tactics_Types.witness =
                           (uu___106_5295.FStar_Tactics_Types.witness);
                         FStar_Tactics_Types.goal_ty =
                           (uu___106_5295.FStar_Tactics_Types.goal_ty);
                         FStar_Tactics_Types.opts =
                           (uu___106_5295.FStar_Tactics_Types.opts);
                         FStar_Tactics_Types.is_guard =
                           (uu___106_5295.FStar_Tactics_Types.is_guard)
                       })))
  
let (revert : Prims.unit tac) =
  bind cur_goal
    (fun goal  ->
       let uu____5303 =
         FStar_TypeChecker_Env.pop_bv goal.FStar_Tactics_Types.context  in
       match uu____5303 with
       | FStar_Pervasives_Native.None  -> fail "Cannot revert; empty context"
       | FStar_Pervasives_Native.Some (x,env') ->
           let typ' =
             let uu____5325 =
               FStar_Syntax_Syntax.mk_Total goal.FStar_Tactics_Types.goal_ty
                in
             FStar_Syntax_Util.arrow [(x, FStar_Pervasives_Native.None)]
               uu____5325
              in
           let w' =
             FStar_Syntax_Util.abs [(x, FStar_Pervasives_Native.None)]
               goal.FStar_Tactics_Types.witness FStar_Pervasives_Native.None
              in
           replace_cur
             (let uu___107_5359 = goal  in
              {
                FStar_Tactics_Types.context = env';
                FStar_Tactics_Types.witness = w';
                FStar_Tactics_Types.goal_ty = typ';
                FStar_Tactics_Types.opts =
                  (uu___107_5359.FStar_Tactics_Types.opts);
                FStar_Tactics_Types.is_guard =
                  (uu___107_5359.FStar_Tactics_Types.is_guard)
              }))
  
let (free_in :
  FStar_Syntax_Syntax.bv -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun bv  ->
    fun t  ->
      let uu____5366 = FStar_Syntax_Free.names t  in
      FStar_Util.set_mem bv uu____5366
  
let rec (clear : FStar_Syntax_Syntax.binder -> Prims.unit tac) =
  fun b  ->
    let bv = FStar_Pervasives_Native.fst b  in
    bind cur_goal
      (fun goal  ->
         mlog
           (fun uu____5382  ->
              let uu____5383 = FStar_Syntax_Print.binder_to_string b  in
              let uu____5384 =
                let uu____5385 =
                  let uu____5386 =
                    FStar_TypeChecker_Env.all_binders
                      goal.FStar_Tactics_Types.context
                     in
                  FStar_All.pipe_right uu____5386 FStar_List.length  in
                FStar_All.pipe_right uu____5385 FStar_Util.string_of_int  in
              FStar_Util.print2 "Clear of (%s), env has %s binders\n"
                uu____5383 uu____5384)
           (fun uu____5397  ->
              let uu____5398 = split_env bv goal.FStar_Tactics_Types.context
                 in
              match uu____5398 with
              | FStar_Pervasives_Native.None  ->
                  fail "Cannot clear; binder not in environment"
              | FStar_Pervasives_Native.Some (e',bvs) ->
                  let rec check1 bvs1 =
                    match bvs1 with
                    | [] -> ret ()
                    | bv'::bvs2 ->
                        let uu____5443 =
                          free_in bv bv'.FStar_Syntax_Syntax.sort  in
                        if uu____5443
                        then
                          let uu____5446 =
                            let uu____5447 =
                              FStar_Syntax_Print.bv_to_string bv'  in
                            FStar_Util.format1
                              "Cannot clear; binder present in the type of %s"
                              uu____5447
                             in
                          fail uu____5446
                        else check1 bvs2
                     in
                  let uu____5449 =
                    free_in bv goal.FStar_Tactics_Types.goal_ty  in
                  if uu____5449
                  then fail "Cannot clear; binder present in goal"
                  else
                    (let uu____5453 = check1 bvs  in
                     bind uu____5453
                       (fun uu____5459  ->
                          let env' = push_bvs e' bvs  in
                          let uu____5461 =
                            new_uvar "clear.witness" env'
                              goal.FStar_Tactics_Types.goal_ty
                             in
                          bind uu____5461
                            (fun ut  ->
                               let uu____5467 =
                                 do_unify goal.FStar_Tactics_Types.context
                                   goal.FStar_Tactics_Types.witness ut
                                  in
                               bind uu____5467
                                 (fun b1  ->
                                    if b1
                                    then
                                      replace_cur
                                        (let uu___108_5476 = goal  in
                                         {
                                           FStar_Tactics_Types.context = env';
                                           FStar_Tactics_Types.witness = ut;
                                           FStar_Tactics_Types.goal_ty =
                                             (uu___108_5476.FStar_Tactics_Types.goal_ty);
                                           FStar_Tactics_Types.opts =
                                             (uu___108_5476.FStar_Tactics_Types.opts);
                                           FStar_Tactics_Types.is_guard =
                                             (uu___108_5476.FStar_Tactics_Types.is_guard)
                                         })
                                    else
                                      fail
                                        "Cannot clear; binder appears in witness"))))))
  
let (clear_top : Prims.unit tac) =
  bind cur_goal
    (fun goal  ->
       let uu____5485 =
         FStar_TypeChecker_Env.pop_bv goal.FStar_Tactics_Types.context  in
       match uu____5485 with
       | FStar_Pervasives_Native.None  -> fail "Cannot clear; empty context"
       | FStar_Pervasives_Native.Some (x,uu____5499) ->
           let uu____5504 = FStar_Syntax_Syntax.mk_binder x  in
           clear uu____5504)
  
let (prune : Prims.string -> Prims.unit tac) =
  fun s  ->
    bind cur_goal
      (fun g  ->
         let ctx = g.FStar_Tactics_Types.context  in
         let ctx' =
           FStar_TypeChecker_Env.rem_proof_ns ctx
             (FStar_Ident.path_of_text s)
            in
         let g' =
           let uu___109_5520 = g  in
           {
             FStar_Tactics_Types.context = ctx';
             FStar_Tactics_Types.witness =
               (uu___109_5520.FStar_Tactics_Types.witness);
             FStar_Tactics_Types.goal_ty =
               (uu___109_5520.FStar_Tactics_Types.goal_ty);
             FStar_Tactics_Types.opts =
               (uu___109_5520.FStar_Tactics_Types.opts);
             FStar_Tactics_Types.is_guard =
               (uu___109_5520.FStar_Tactics_Types.is_guard)
           }  in
         bind __dismiss (fun uu____5522  -> add_goals [g']))
  
let (addns : Prims.string -> Prims.unit tac) =
  fun s  ->
    bind cur_goal
      (fun g  ->
         let ctx = g.FStar_Tactics_Types.context  in
         let ctx' =
           FStar_TypeChecker_Env.add_proof_ns ctx
             (FStar_Ident.path_of_text s)
            in
         let g' =
           let uu___110_5538 = g  in
           {
             FStar_Tactics_Types.context = ctx';
             FStar_Tactics_Types.witness =
               (uu___110_5538.FStar_Tactics_Types.witness);
             FStar_Tactics_Types.goal_ty =
               (uu___110_5538.FStar_Tactics_Types.goal_ty);
             FStar_Tactics_Types.opts =
               (uu___110_5538.FStar_Tactics_Types.opts);
             FStar_Tactics_Types.is_guard =
               (uu___110_5538.FStar_Tactics_Types.is_guard)
           }  in
         bind __dismiss (fun uu____5540  -> add_goals [g']))
  
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
            let uu____5572 = FStar_Syntax_Subst.compress t  in
            uu____5572.FStar_Syntax_Syntax.n  in
          let uu____5575 =
            if d = FStar_Tactics_Types.TopDown
            then
              f env
                (let uu___114_5581 = t  in
                 {
                   FStar_Syntax_Syntax.n = tn;
                   FStar_Syntax_Syntax.pos =
                     (uu___114_5581.FStar_Syntax_Syntax.pos);
                   FStar_Syntax_Syntax.vars =
                     (uu___114_5581.FStar_Syntax_Syntax.vars)
                 })
            else ret t  in
          bind uu____5575
            (fun t1  ->
               let ff = tac_fold_env d f env  in
               let tn1 =
                 let uu____5595 =
                   let uu____5596 = FStar_Syntax_Subst.compress t1  in
                   uu____5596.FStar_Syntax_Syntax.n  in
                 match uu____5595 with
                 | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
                     let uu____5623 = ff hd1  in
                     bind uu____5623
                       (fun hd2  ->
                          let fa uu____5643 =
                            match uu____5643 with
                            | (a,q) ->
                                let uu____5656 = ff a  in
                                bind uu____5656 (fun a1  -> ret (a1, q))
                             in
                          let uu____5669 = mapM fa args  in
                          bind uu____5669
                            (fun args1  ->
                               ret (FStar_Syntax_Syntax.Tm_app (hd2, args1))))
                 | FStar_Syntax_Syntax.Tm_abs (bs,t2,k) ->
                     let uu____5729 = FStar_Syntax_Subst.open_term bs t2  in
                     (match uu____5729 with
                      | (bs1,t') ->
                          let uu____5738 =
                            let uu____5741 =
                              FStar_TypeChecker_Env.push_binders env bs1  in
                            tac_fold_env d f uu____5741 t'  in
                          bind uu____5738
                            (fun t''  ->
                               let uu____5745 =
                                 let uu____5746 =
                                   let uu____5763 =
                                     FStar_Syntax_Subst.close_binders bs1  in
                                   let uu____5764 =
                                     FStar_Syntax_Subst.close bs1 t''  in
                                   (uu____5763, uu____5764, k)  in
                                 FStar_Syntax_Syntax.Tm_abs uu____5746  in
                               ret uu____5745))
                 | FStar_Syntax_Syntax.Tm_arrow (bs,k) -> ret tn
                 | FStar_Syntax_Syntax.Tm_match (hd1,brs) ->
                     let uu____5823 = ff hd1  in
                     bind uu____5823
                       (fun hd2  ->
                          let ffb br =
                            let uu____5836 =
                              FStar_Syntax_Subst.open_branch br  in
                            match uu____5836 with
                            | (pat,w,e) ->
                                let uu____5858 = ff e  in
                                bind uu____5858
                                  (fun e1  ->
                                     let br1 =
                                       FStar_Syntax_Subst.close_branch
                                         (pat, w, e1)
                                        in
                                     ret br1)
                             in
                          let uu____5871 = mapM ffb brs  in
                          bind uu____5871
                            (fun brs1  ->
                               ret (FStar_Syntax_Syntax.Tm_match (hd2, brs1))))
                 | FStar_Syntax_Syntax.Tm_let
                     ((false
                       ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl bv;
                          FStar_Syntax_Syntax.lbunivs = uu____5885;
                          FStar_Syntax_Syntax.lbtyp = uu____5886;
                          FStar_Syntax_Syntax.lbeff = uu____5887;
                          FStar_Syntax_Syntax.lbdef = def;
                          FStar_Syntax_Syntax.lbattrs = uu____5889;
                          FStar_Syntax_Syntax.lbpos = uu____5890;_}::[]),e)
                     ->
                     let lb =
                       let uu____5915 =
                         let uu____5916 = FStar_Syntax_Subst.compress t1  in
                         uu____5916.FStar_Syntax_Syntax.n  in
                       match uu____5915 with
                       | FStar_Syntax_Syntax.Tm_let
                           ((false ,lb::[]),uu____5920) -> lb
                       | uu____5933 -> failwith "impossible"  in
                     let fflb lb1 =
                       let uu____5940 = ff lb1.FStar_Syntax_Syntax.lbdef  in
                       bind uu____5940
                         (fun def1  ->
                            ret
                              (let uu___111_5946 = lb1  in
                               {
                                 FStar_Syntax_Syntax.lbname =
                                   (uu___111_5946.FStar_Syntax_Syntax.lbname);
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___111_5946.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp =
                                   (uu___111_5946.FStar_Syntax_Syntax.lbtyp);
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___111_5946.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def1;
                                 FStar_Syntax_Syntax.lbattrs =
                                   (uu___111_5946.FStar_Syntax_Syntax.lbattrs);
                                 FStar_Syntax_Syntax.lbpos =
                                   (uu___111_5946.FStar_Syntax_Syntax.lbpos)
                               }))
                        in
                     let uu____5947 = fflb lb  in
                     bind uu____5947
                       (fun lb1  ->
                          let uu____5956 =
                            let uu____5961 =
                              let uu____5962 =
                                FStar_Syntax_Syntax.mk_binder bv  in
                              [uu____5962]  in
                            FStar_Syntax_Subst.open_term uu____5961 e  in
                          match uu____5956 with
                          | (bs,e1) ->
                              let uu____5967 = ff e1  in
                              bind uu____5967
                                (fun e2  ->
                                   let e3 = FStar_Syntax_Subst.close bs e2
                                      in
                                   ret
                                     (FStar_Syntax_Syntax.Tm_let
                                        ((false, [lb1]), e3))))
                 | FStar_Syntax_Syntax.Tm_let ((true ,lbs),e) ->
                     let fflb lb =
                       let uu____6004 = ff lb.FStar_Syntax_Syntax.lbdef  in
                       bind uu____6004
                         (fun def  ->
                            ret
                              (let uu___112_6010 = lb  in
                               {
                                 FStar_Syntax_Syntax.lbname =
                                   (uu___112_6010.FStar_Syntax_Syntax.lbname);
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___112_6010.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp =
                                   (uu___112_6010.FStar_Syntax_Syntax.lbtyp);
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___112_6010.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def;
                                 FStar_Syntax_Syntax.lbattrs =
                                   (uu___112_6010.FStar_Syntax_Syntax.lbattrs);
                                 FStar_Syntax_Syntax.lbpos =
                                   (uu___112_6010.FStar_Syntax_Syntax.lbpos)
                               }))
                        in
                     let uu____6011 = FStar_Syntax_Subst.open_let_rec lbs e
                        in
                     (match uu____6011 with
                      | (lbs1,e1) ->
                          let uu____6026 = mapM fflb lbs1  in
                          bind uu____6026
                            (fun lbs2  ->
                               let uu____6038 = ff e1  in
                               bind uu____6038
                                 (fun e2  ->
                                    let uu____6046 =
                                      FStar_Syntax_Subst.close_let_rec lbs2
                                        e2
                                       in
                                    match uu____6046 with
                                    | (lbs3,e3) ->
                                        ret
                                          (FStar_Syntax_Syntax.Tm_let
                                             ((true, lbs3), e3)))))
                 | FStar_Syntax_Syntax.Tm_ascribed (t2,asc,eff) ->
                     let uu____6112 = ff t2  in
                     bind uu____6112
                       (fun t3  ->
                          ret
                            (FStar_Syntax_Syntax.Tm_ascribed (t3, asc, eff)))
                 | FStar_Syntax_Syntax.Tm_meta (t2,m) ->
                     let uu____6141 = ff t2  in
                     bind uu____6141
                       (fun t3  -> ret (FStar_Syntax_Syntax.Tm_meta (t3, m)))
                 | uu____6146 -> ret tn  in
               bind tn1
                 (fun tn2  ->
                    let t' =
                      let uu___113_6153 = t1  in
                      {
                        FStar_Syntax_Syntax.n = tn2;
                        FStar_Syntax_Syntax.pos =
                          (uu___113_6153.FStar_Syntax_Syntax.pos);
                        FStar_Syntax_Syntax.vars =
                          (uu___113_6153.FStar_Syntax_Syntax.vars)
                      }  in
                    if d = FStar_Tactics_Types.BottomUp
                    then f env t'
                    else ret t'))
  
let (pointwise_rec :
  FStar_Tactics_Types.proofstate ->
    Prims.unit tac ->
      FStar_Options.optionstate ->
        FStar_TypeChecker_Env.env ->
          FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac)
  =
  fun ps  ->
    fun tau  ->
      fun opts  ->
        fun env  ->
          fun t  ->
            let uu____6182 = FStar_TypeChecker_TcTerm.tc_term env t  in
            match uu____6182 with
            | (t1,lcomp,g) ->
                let uu____6194 =
                  (let uu____6197 =
                     FStar_Syntax_Util.is_pure_or_ghost_lcomp lcomp  in
                   Prims.op_Negation uu____6197) ||
                    (let uu____6199 = FStar_TypeChecker_Rel.is_trivial g  in
                     Prims.op_Negation uu____6199)
                   in
                if uu____6194
                then ret t1
                else
                  (let rewrite_eq =
                     let typ = lcomp.FStar_Syntax_Syntax.res_typ  in
                     let uu____6209 = new_uvar "pointwise_rec" env typ  in
                     bind uu____6209
                       (fun ut  ->
                          log ps
                            (fun uu____6220  ->
                               let uu____6221 =
                                 FStar_Syntax_Print.term_to_string t1  in
                               let uu____6222 =
                                 FStar_Syntax_Print.term_to_string ut  in
                               FStar_Util.print2
                                 "Pointwise_rec: making equality\n\t%s ==\n\t%s\n"
                                 uu____6221 uu____6222);
                          (let uu____6223 =
                             let uu____6226 =
                               let uu____6227 =
                                 FStar_TypeChecker_TcTerm.universe_of env typ
                                  in
                               FStar_Syntax_Util.mk_eq2 uu____6227 typ t1 ut
                                in
                             add_irrelevant_goal "pointwise_rec equation" env
                               uu____6226 opts
                              in
                           bind uu____6223
                             (fun uu____6230  ->
                                let uu____6231 =
                                  bind tau
                                    (fun uu____6237  ->
                                       let ut1 =
                                         FStar_TypeChecker_Normalize.reduce_uvar_solutions
                                           env ut
                                          in
                                       log ps
                                         (fun uu____6243  ->
                                            let uu____6244 =
                                              FStar_Syntax_Print.term_to_string
                                                t1
                                               in
                                            let uu____6245 =
                                              FStar_Syntax_Print.term_to_string
                                                ut1
                                               in
                                            FStar_Util.print2
                                              "Pointwise_rec: succeeded rewriting\n\t%s to\n\t%s\n"
                                              uu____6244 uu____6245);
                                       ret ut1)
                                   in
                                focus uu____6231)))
                      in
                   let uu____6246 = trytac' rewrite_eq  in
                   bind uu____6246
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
          let uu____6394 = FStar_Syntax_Subst.compress t  in
          maybe_continue ctrl uu____6394
            (fun t1  ->
               let uu____6398 =
                 f env
                   (let uu___117_6407 = t1  in
                    {
                      FStar_Syntax_Syntax.n = (t1.FStar_Syntax_Syntax.n);
                      FStar_Syntax_Syntax.pos =
                        (uu___117_6407.FStar_Syntax_Syntax.pos);
                      FStar_Syntax_Syntax.vars =
                        (uu___117_6407.FStar_Syntax_Syntax.vars)
                    })
                  in
               bind uu____6398
                 (fun uu____6419  ->
                    match uu____6419 with
                    | (t2,ctrl1) ->
                        maybe_continue ctrl1 t2
                          (fun t3  ->
                             let uu____6438 =
                               let uu____6439 =
                                 FStar_Syntax_Subst.compress t3  in
                               uu____6439.FStar_Syntax_Syntax.n  in
                             match uu____6438 with
                             | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
                                 let uu____6472 =
                                   ctrl_tac_fold f env ctrl1 hd1  in
                                 bind uu____6472
                                   (fun uu____6497  ->
                                      match uu____6497 with
                                      | (hd2,ctrl2) ->
                                          let ctrl3 = keep_going ctrl2  in
                                          let uu____6513 =
                                            ctrl_tac_fold_args f env ctrl3
                                              args
                                             in
                                          bind uu____6513
                                            (fun uu____6540  ->
                                               match uu____6540 with
                                               | (args1,ctrl4) ->
                                                   ret
                                                     ((let uu___115_6570 = t3
                                                          in
                                                       {
                                                         FStar_Syntax_Syntax.n
                                                           =
                                                           (FStar_Syntax_Syntax.Tm_app
                                                              (hd2, args1));
                                                         FStar_Syntax_Syntax.pos
                                                           =
                                                           (uu___115_6570.FStar_Syntax_Syntax.pos);
                                                         FStar_Syntax_Syntax.vars
                                                           =
                                                           (uu___115_6570.FStar_Syntax_Syntax.vars)
                                                       }), ctrl4)))
                             | FStar_Syntax_Syntax.Tm_abs (bs,t4,k) ->
                                 let uu____6596 =
                                   FStar_Syntax_Subst.open_term bs t4  in
                                 (match uu____6596 with
                                  | (bs1,t') ->
                                      let uu____6611 =
                                        let uu____6618 =
                                          FStar_TypeChecker_Env.push_binders
                                            env bs1
                                           in
                                        ctrl_tac_fold f uu____6618 ctrl1 t'
                                         in
                                      bind uu____6611
                                        (fun uu____6636  ->
                                           match uu____6636 with
                                           | (t'',ctrl2) ->
                                               let uu____6651 =
                                                 let uu____6658 =
                                                   let uu___116_6661 = t4  in
                                                   let uu____6664 =
                                                     let uu____6665 =
                                                       let uu____6682 =
                                                         FStar_Syntax_Subst.close_binders
                                                           bs1
                                                          in
                                                       let uu____6683 =
                                                         FStar_Syntax_Subst.close
                                                           bs1 t''
                                                          in
                                                       (uu____6682,
                                                         uu____6683, k)
                                                        in
                                                     FStar_Syntax_Syntax.Tm_abs
                                                       uu____6665
                                                      in
                                                   {
                                                     FStar_Syntax_Syntax.n =
                                                       uu____6664;
                                                     FStar_Syntax_Syntax.pos
                                                       =
                                                       (uu___116_6661.FStar_Syntax_Syntax.pos);
                                                     FStar_Syntax_Syntax.vars
                                                       =
                                                       (uu___116_6661.FStar_Syntax_Syntax.vars)
                                                   }  in
                                                 (uu____6658, ctrl2)  in
                                               ret uu____6651))
                             | FStar_Syntax_Syntax.Tm_arrow (bs,k) ->
                                 ret (t3, ctrl1)
                             | uu____6716 -> ret (t3, ctrl1))))

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
              let uu____6767 = ctrl_tac_fold f env ctrl t  in
              bind uu____6767
                (fun uu____6795  ->
                   match uu____6795 with
                   | (t1,ctrl1) ->
                       let uu____6814 = ctrl_tac_fold_args f env ctrl1 ts1
                          in
                       bind uu____6814
                         (fun uu____6845  ->
                            match uu____6845 with
                            | (ts2,ctrl2) -> ret (((t1, q) :: ts2), ctrl2)))

let (rewrite_rec :
  FStar_Tactics_Types.proofstate ->
    (FStar_Syntax_Syntax.term -> rewrite_result ctrl_tac) ->
      Prims.unit tac ->
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
              let uu____6929 =
                let uu____6936 =
                  add_irrelevant_goal "dummy" env FStar_Syntax_Util.t_true
                    opts
                   in
                bind uu____6936
                  (fun uu____6945  ->
                     let uu____6946 = ctrl t1  in
                     bind uu____6946
                       (fun res  -> bind trivial (fun uu____6973  -> ret res)))
                 in
              bind uu____6929
                (fun uu____6989  ->
                   match uu____6989 with
                   | (should_rewrite,ctrl1) ->
                       if Prims.op_Negation should_rewrite
                       then ret (t1, ctrl1)
                       else
                         (let uu____7013 =
                            FStar_TypeChecker_TcTerm.tc_term env t1  in
                          match uu____7013 with
                          | (t2,lcomp,g) ->
                              let uu____7029 =
                                (let uu____7032 =
                                   FStar_Syntax_Util.is_pure_or_ghost_lcomp
                                     lcomp
                                    in
                                 Prims.op_Negation uu____7032) ||
                                  (let uu____7034 =
                                     FStar_TypeChecker_Rel.is_trivial g  in
                                   Prims.op_Negation uu____7034)
                                 in
                              if uu____7029
                              then ret (t2, globalStop)
                              else
                                (let typ = lcomp.FStar_Syntax_Syntax.res_typ
                                    in
                                 let uu____7049 =
                                   new_uvar "pointwise_rec" env typ  in
                                 bind uu____7049
                                   (fun ut  ->
                                      log ps
                                        (fun uu____7064  ->
                                           let uu____7065 =
                                             FStar_Syntax_Print.term_to_string
                                               t2
                                              in
                                           let uu____7066 =
                                             FStar_Syntax_Print.term_to_string
                                               ut
                                              in
                                           FStar_Util.print2
                                             "Pointwise_rec: making equality\n\t%s ==\n\t%s\n"
                                             uu____7065 uu____7066);
                                      (let uu____7067 =
                                         let uu____7070 =
                                           let uu____7071 =
                                             FStar_TypeChecker_TcTerm.universe_of
                                               env typ
                                              in
                                           FStar_Syntax_Util.mk_eq2
                                             uu____7071 typ t2 ut
                                            in
                                         add_irrelevant_goal
                                           "rewrite_rec equation" env
                                           uu____7070 opts
                                          in
                                       bind uu____7067
                                         (fun uu____7078  ->
                                            let uu____7079 =
                                              bind rewriter
                                                (fun uu____7093  ->
                                                   let ut1 =
                                                     FStar_TypeChecker_Normalize.reduce_uvar_solutions
                                                       env ut
                                                      in
                                                   log ps
                                                     (fun uu____7099  ->
                                                        let uu____7100 =
                                                          FStar_Syntax_Print.term_to_string
                                                            t2
                                                           in
                                                        let uu____7101 =
                                                          FStar_Syntax_Print.term_to_string
                                                            ut1
                                                           in
                                                        FStar_Util.print2
                                                          "rewrite_rec: succeeded rewriting\n\t%s to\n\t%s\n"
                                                          uu____7100
                                                          uu____7101);
                                                   ret (ut1, ctrl1))
                                               in
                                            focus uu____7079))))))
  
let (topdown_rewrite :
  (FStar_Syntax_Syntax.term ->
     (Prims.bool,FStar_BigInt.t) FStar_Pervasives_Native.tuple2 tac)
    -> Prims.unit tac -> Prims.unit tac)
  =
  fun ctrl  ->
    fun rewriter  ->
      bind get
        (fun ps  ->
           let uu____7145 =
             match ps.FStar_Tactics_Types.goals with
             | g::gs -> (g, gs)
             | [] -> failwith "Pointwise: no goals"  in
           match uu____7145 with
           | (g,gs) ->
               let gt1 = g.FStar_Tactics_Types.goal_ty  in
               (log ps
                  (fun uu____7182  ->
                     let uu____7183 = FStar_Syntax_Print.term_to_string gt1
                        in
                     FStar_Util.print1 "Pointwise starting with %s\n"
                       uu____7183);
                bind dismiss_all
                  (fun uu____7186  ->
                     let uu____7187 =
                       ctrl_tac_fold
                         (rewrite_rec ps ctrl rewriter
                            g.FStar_Tactics_Types.opts)
                         g.FStar_Tactics_Types.context keepGoing gt1
                        in
                     bind uu____7187
                       (fun uu____7205  ->
                          match uu____7205 with
                          | (gt',uu____7213) ->
                              (log ps
                                 (fun uu____7217  ->
                                    let uu____7218 =
                                      FStar_Syntax_Print.term_to_string gt'
                                       in
                                    FStar_Util.print1
                                      "Pointwise seems to have succeded with %s\n"
                                      uu____7218);
                               (let uu____7219 = push_goals gs  in
                                bind uu____7219
                                  (fun uu____7223  ->
                                     add_goals
                                       [(let uu___118_7225 = g  in
                                         {
                                           FStar_Tactics_Types.context =
                                             (uu___118_7225.FStar_Tactics_Types.context);
                                           FStar_Tactics_Types.witness =
                                             (uu___118_7225.FStar_Tactics_Types.witness);
                                           FStar_Tactics_Types.goal_ty = gt';
                                           FStar_Tactics_Types.opts =
                                             (uu___118_7225.FStar_Tactics_Types.opts);
                                           FStar_Tactics_Types.is_guard =
                                             (uu___118_7225.FStar_Tactics_Types.is_guard)
                                         })])))))))
  
let (pointwise :
  FStar_Tactics_Types.direction -> Prims.unit tac -> Prims.unit tac) =
  fun d  ->
    fun tau  ->
      bind get
        (fun ps  ->
           let uu____7247 =
             match ps.FStar_Tactics_Types.goals with
             | g::gs -> (g, gs)
             | [] -> failwith "Pointwise: no goals"  in
           match uu____7247 with
           | (g,gs) ->
               let gt1 = g.FStar_Tactics_Types.goal_ty  in
               (log ps
                  (fun uu____7284  ->
                     let uu____7285 = FStar_Syntax_Print.term_to_string gt1
                        in
                     FStar_Util.print1 "Pointwise starting with %s\n"
                       uu____7285);
                bind dismiss_all
                  (fun uu____7288  ->
                     let uu____7289 =
                       tac_fold_env d
                         (pointwise_rec ps tau g.FStar_Tactics_Types.opts)
                         g.FStar_Tactics_Types.context gt1
                        in
                     bind uu____7289
                       (fun gt'  ->
                          log ps
                            (fun uu____7299  ->
                               let uu____7300 =
                                 FStar_Syntax_Print.term_to_string gt'  in
                               FStar_Util.print1
                                 "Pointwise seems to have succeded with %s\n"
                                 uu____7300);
                          (let uu____7301 = push_goals gs  in
                           bind uu____7301
                             (fun uu____7305  ->
                                add_goals
                                  [(let uu___119_7307 = g  in
                                    {
                                      FStar_Tactics_Types.context =
                                        (uu___119_7307.FStar_Tactics_Types.context);
                                      FStar_Tactics_Types.witness =
                                        (uu___119_7307.FStar_Tactics_Types.witness);
                                      FStar_Tactics_Types.goal_ty = gt';
                                      FStar_Tactics_Types.opts =
                                        (uu___119_7307.FStar_Tactics_Types.opts);
                                      FStar_Tactics_Types.is_guard =
                                        (uu___119_7307.FStar_Tactics_Types.is_guard)
                                    })]))))))
  
let (trefl : Prims.unit tac) =
  bind cur_goal
    (fun g  ->
       let uu____7327 =
         FStar_Syntax_Util.un_squash g.FStar_Tactics_Types.goal_ty  in
       match uu____7327 with
       | FStar_Pervasives_Native.Some t ->
           let uu____7339 = FStar_Syntax_Util.head_and_args' t  in
           (match uu____7339 with
            | (hd1,args) ->
                let uu____7372 =
                  let uu____7385 =
                    let uu____7386 = FStar_Syntax_Util.un_uinst hd1  in
                    uu____7386.FStar_Syntax_Syntax.n  in
                  (uu____7385, args)  in
                (match uu____7372 with
                 | (FStar_Syntax_Syntax.Tm_fvar
                    fv,uu____7400::(l,uu____7402)::(r,uu____7404)::[]) when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.eq2_lid
                     ->
                     let uu____7451 =
                       do_unify g.FStar_Tactics_Types.context l r  in
                     bind uu____7451
                       (fun b  ->
                          if Prims.op_Negation b
                          then
                            let uu____7460 =
                              tts g.FStar_Tactics_Types.context l  in
                            let uu____7461 =
                              tts g.FStar_Tactics_Types.context r  in
                            fail2 "trefl: not a trivial equality (%s vs %s)"
                              uu____7460 uu____7461
                          else solve g FStar_Syntax_Util.exp_unit)
                 | (hd2,uu____7464) ->
                     let uu____7481 = tts g.FStar_Tactics_Types.context t  in
                     fail1 "trefl: not an equality (%s)" uu____7481))
       | FStar_Pervasives_Native.None  -> fail "not an irrelevant goal")
  
let (dup : Prims.unit tac) =
  bind cur_goal
    (fun g  ->
       let uu____7491 =
         new_uvar "dup" g.FStar_Tactics_Types.context
           g.FStar_Tactics_Types.goal_ty
          in
       bind uu____7491
         (fun u  ->
            let g' =
              let uu___120_7498 = g  in
              {
                FStar_Tactics_Types.context =
                  (uu___120_7498.FStar_Tactics_Types.context);
                FStar_Tactics_Types.witness = u;
                FStar_Tactics_Types.goal_ty =
                  (uu___120_7498.FStar_Tactics_Types.goal_ty);
                FStar_Tactics_Types.opts =
                  (uu___120_7498.FStar_Tactics_Types.opts);
                FStar_Tactics_Types.is_guard =
                  (uu___120_7498.FStar_Tactics_Types.is_guard)
              }  in
            bind __dismiss
              (fun uu____7501  ->
                 let uu____7502 =
                   let uu____7505 =
                     let uu____7506 =
                       FStar_TypeChecker_TcTerm.universe_of
                         g.FStar_Tactics_Types.context
                         g.FStar_Tactics_Types.goal_ty
                        in
                     FStar_Syntax_Util.mk_eq2 uu____7506
                       g.FStar_Tactics_Types.goal_ty u
                       g.FStar_Tactics_Types.witness
                      in
                   add_irrelevant_goal "dup equation"
                     g.FStar_Tactics_Types.context uu____7505
                     g.FStar_Tactics_Types.opts
                    in
                 bind uu____7502
                   (fun uu____7509  ->
                      let uu____7510 = add_goals [g']  in
                      bind uu____7510 (fun uu____7514  -> ret ())))))
  
let (flip : Prims.unit tac) =
  bind get
    (fun ps  ->
       match ps.FStar_Tactics_Types.goals with
       | g1::g2::gs ->
           set
             (let uu___121_7533 = ps  in
              {
                FStar_Tactics_Types.main_context =
                  (uu___121_7533.FStar_Tactics_Types.main_context);
                FStar_Tactics_Types.main_goal =
                  (uu___121_7533.FStar_Tactics_Types.main_goal);
                FStar_Tactics_Types.all_implicits =
                  (uu___121_7533.FStar_Tactics_Types.all_implicits);
                FStar_Tactics_Types.goals = (g2 :: g1 :: gs);
                FStar_Tactics_Types.smt_goals =
                  (uu___121_7533.FStar_Tactics_Types.smt_goals);
                FStar_Tactics_Types.depth =
                  (uu___121_7533.FStar_Tactics_Types.depth);
                FStar_Tactics_Types.__dump =
                  (uu___121_7533.FStar_Tactics_Types.__dump);
                FStar_Tactics_Types.psc =
                  (uu___121_7533.FStar_Tactics_Types.psc);
                FStar_Tactics_Types.entry_range =
                  (uu___121_7533.FStar_Tactics_Types.entry_range);
                FStar_Tactics_Types.guard_policy =
                  (uu___121_7533.FStar_Tactics_Types.guard_policy);
                FStar_Tactics_Types.freshness =
                  (uu___121_7533.FStar_Tactics_Types.freshness)
              })
       | uu____7534 -> fail "flip: less than 2 goals")
  
let (later : Prims.unit tac) =
  bind get
    (fun ps  ->
       match ps.FStar_Tactics_Types.goals with
       | [] -> ret ()
       | g::gs ->
           set
             (let uu___122_7551 = ps  in
              {
                FStar_Tactics_Types.main_context =
                  (uu___122_7551.FStar_Tactics_Types.main_context);
                FStar_Tactics_Types.main_goal =
                  (uu___122_7551.FStar_Tactics_Types.main_goal);
                FStar_Tactics_Types.all_implicits =
                  (uu___122_7551.FStar_Tactics_Types.all_implicits);
                FStar_Tactics_Types.goals = (FStar_List.append gs [g]);
                FStar_Tactics_Types.smt_goals =
                  (uu___122_7551.FStar_Tactics_Types.smt_goals);
                FStar_Tactics_Types.depth =
                  (uu___122_7551.FStar_Tactics_Types.depth);
                FStar_Tactics_Types.__dump =
                  (uu___122_7551.FStar_Tactics_Types.__dump);
                FStar_Tactics_Types.psc =
                  (uu___122_7551.FStar_Tactics_Types.psc);
                FStar_Tactics_Types.entry_range =
                  (uu___122_7551.FStar_Tactics_Types.entry_range);
                FStar_Tactics_Types.guard_policy =
                  (uu___122_7551.FStar_Tactics_Types.guard_policy);
                FStar_Tactics_Types.freshness =
                  (uu___122_7551.FStar_Tactics_Types.freshness)
              }))
  
let (qed : Prims.unit tac) =
  bind get
    (fun ps  ->
       match ps.FStar_Tactics_Types.goals with
       | [] -> ret ()
       | uu____7560 -> fail "Not done!")
  
let (cases :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 tac)
  =
  fun t  ->
    let uu____7578 =
      bind cur_goal
        (fun g  ->
           let uu____7592 = __tc g.FStar_Tactics_Types.context t  in
           bind uu____7592
             (fun uu____7628  ->
                match uu____7628 with
                | (t1,typ,guard) ->
                    let uu____7644 = FStar_Syntax_Util.head_and_args typ  in
                    (match uu____7644 with
                     | (hd1,args) ->
                         let uu____7687 =
                           let uu____7700 =
                             let uu____7701 = FStar_Syntax_Util.un_uinst hd1
                                in
                             uu____7701.FStar_Syntax_Syntax.n  in
                           (uu____7700, args)  in
                         (match uu____7687 with
                          | (FStar_Syntax_Syntax.Tm_fvar
                             fv,(p,uu____7720)::(q,uu____7722)::[]) when
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
                                let uu___123_7760 = g  in
                                let uu____7761 =
                                  FStar_TypeChecker_Env.push_bv
                                    g.FStar_Tactics_Types.context v_p
                                   in
                                {
                                  FStar_Tactics_Types.context = uu____7761;
                                  FStar_Tactics_Types.witness =
                                    (uu___123_7760.FStar_Tactics_Types.witness);
                                  FStar_Tactics_Types.goal_ty =
                                    (uu___123_7760.FStar_Tactics_Types.goal_ty);
                                  FStar_Tactics_Types.opts =
                                    (uu___123_7760.FStar_Tactics_Types.opts);
                                  FStar_Tactics_Types.is_guard =
                                    (uu___123_7760.FStar_Tactics_Types.is_guard)
                                }  in
                              let g2 =
                                let uu___124_7763 = g  in
                                let uu____7764 =
                                  FStar_TypeChecker_Env.push_bv
                                    g.FStar_Tactics_Types.context v_q
                                   in
                                {
                                  FStar_Tactics_Types.context = uu____7764;
                                  FStar_Tactics_Types.witness =
                                    (uu___124_7763.FStar_Tactics_Types.witness);
                                  FStar_Tactics_Types.goal_ty =
                                    (uu___124_7763.FStar_Tactics_Types.goal_ty);
                                  FStar_Tactics_Types.opts =
                                    (uu___124_7763.FStar_Tactics_Types.opts);
                                  FStar_Tactics_Types.is_guard =
                                    (uu___124_7763.FStar_Tactics_Types.is_guard)
                                }  in
                              bind __dismiss
                                (fun uu____7771  ->
                                   let uu____7772 = add_goals [g1; g2]  in
                                   bind uu____7772
                                     (fun uu____7781  ->
                                        let uu____7782 =
                                          let uu____7787 =
                                            FStar_Syntax_Syntax.bv_to_name
                                              v_p
                                             in
                                          let uu____7788 =
                                            FStar_Syntax_Syntax.bv_to_name
                                              v_q
                                             in
                                          (uu____7787, uu____7788)  in
                                        ret uu____7782))
                          | uu____7793 ->
                              let uu____7806 =
                                tts g.FStar_Tactics_Types.context typ  in
                              fail1 "Not a disjunction: %s" uu____7806))))
       in
    FStar_All.pipe_left (wrap_err "cases") uu____7578
  
let (set_options : Prims.string -> Prims.unit tac) =
  fun s  ->
    bind cur_goal
      (fun g  ->
         FStar_Options.push ();
         (let uu____7844 = FStar_Util.smap_copy g.FStar_Tactics_Types.opts
             in
          FStar_Options.set uu____7844);
         (let res = FStar_Options.set_options FStar_Options.Set s  in
          let opts' = FStar_Options.peek ()  in
          FStar_Options.pop ();
          (match res with
           | FStar_Getopt.Success  ->
               let g' =
                 let uu___125_7851 = g  in
                 {
                   FStar_Tactics_Types.context =
                     (uu___125_7851.FStar_Tactics_Types.context);
                   FStar_Tactics_Types.witness =
                     (uu___125_7851.FStar_Tactics_Types.witness);
                   FStar_Tactics_Types.goal_ty =
                     (uu___125_7851.FStar_Tactics_Types.goal_ty);
                   FStar_Tactics_Types.opts = opts';
                   FStar_Tactics_Types.is_guard =
                     (uu___125_7851.FStar_Tactics_Types.is_guard)
                 }  in
               replace_cur g'
           | FStar_Getopt.Error err ->
               fail2 "Setting options `%s` failed: %s" s err
           | FStar_Getopt.Help  ->
               fail1 "Setting options `%s` failed (got `Help`?)" s)))
  
let (top_env : FStar_TypeChecker_Env.env tac) =
  bind get
    (fun ps  -> FStar_All.pipe_left ret ps.FStar_Tactics_Types.main_context)
  
let (cur_env : FStar_TypeChecker_Env.env tac) =
  bind cur_goal
    (fun g  -> FStar_All.pipe_left ret g.FStar_Tactics_Types.context)
  
let (cur_goal' : FStar_Syntax_Syntax.typ tac) =
  bind cur_goal
    (fun g  -> FStar_All.pipe_left ret g.FStar_Tactics_Types.goal_ty)
  
let (cur_witness : FStar_Syntax_Syntax.term tac) =
  bind cur_goal
    (fun g  -> FStar_All.pipe_left ret g.FStar_Tactics_Types.witness)
  
let (unquote :
  FStar_Reflection_Data.typ ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac)
  =
  fun ty  ->
    fun tm  ->
      let uu____7895 =
        bind cur_goal
          (fun goal  ->
             let env =
               FStar_TypeChecker_Env.set_expected_typ
                 goal.FStar_Tactics_Types.context ty
                in
             let uu____7903 = __tc env tm  in
             bind uu____7903
               (fun uu____7923  ->
                  match uu____7923 with
                  | (tm1,typ,guard) ->
                      let uu____7935 =
                        proc_guard "unquote" env guard
                          goal.FStar_Tactics_Types.opts
                         in
                      bind uu____7935 (fun uu____7939  -> ret tm1)))
         in
      FStar_All.pipe_left (wrap_err "unquote") uu____7895
  
let (uvar_env :
  env ->
    FStar_Reflection_Data.typ FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.term tac)
  =
  fun env  ->
    fun ty  ->
      let uu____7958 =
        match ty with
        | FStar_Pervasives_Native.Some ty1 -> ret ty1
        | FStar_Pervasives_Native.None  ->
            let uu____7964 =
              let uu____7965 = FStar_Syntax_Util.type_u ()  in
              FStar_All.pipe_left FStar_Pervasives_Native.fst uu____7965  in
            new_uvar "uvar_env.2" env uu____7964
         in
      bind uu____7958
        (fun typ  ->
           let uu____7977 = new_uvar "uvar_env" env typ  in
           bind uu____7977 (fun t  -> ret t))
  
let (unshelve : FStar_Syntax_Syntax.term -> Prims.unit tac) =
  fun t  ->
    let uu____7989 =
      bind get
        (fun ps  ->
           let env = ps.FStar_Tactics_Types.main_context  in
           let opts =
             match ps.FStar_Tactics_Types.goals with
             | g::uu____8000 -> g.FStar_Tactics_Types.opts
             | uu____8003 -> FStar_Options.peek ()  in
           let uu____8006 = __tc env t  in
           bind uu____8006
             (fun uu____8026  ->
                match uu____8026 with
                | (t1,typ,guard) ->
                    let uu____8038 = proc_guard "unshelve" env guard opts  in
                    bind uu____8038
                      (fun uu____8043  ->
                         let uu____8044 =
                           let uu____8047 =
                             let uu____8048 = bnorm env t1  in
                             let uu____8049 = bnorm env typ  in
                             {
                               FStar_Tactics_Types.context = env;
                               FStar_Tactics_Types.witness = uu____8048;
                               FStar_Tactics_Types.goal_ty = uu____8049;
                               FStar_Tactics_Types.opts = opts;
                               FStar_Tactics_Types.is_guard = false
                             }  in
                           [uu____8047]  in
                         add_goals uu____8044)))
       in
    FStar_All.pipe_left (wrap_err "unshelve") uu____7989
  
let (unify :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool tac) =
  fun t1  ->
    fun t2  ->
      bind get
        (fun ps  -> do_unify ps.FStar_Tactics_Types.main_context t1 t2)
  
let (launch_process :
  Prims.string -> Prims.string -> Prims.string -> Prims.string tac) =
  fun prog  ->
    fun args  ->
      fun input  ->
        bind idtac
          (fun uu____8082  ->
             let uu____8083 = FStar_Options.unsafe_tactic_exec ()  in
             if uu____8083
             then
               let s =
                 FStar_Util.launch_process true "tactic_launch" prog args
                   input (fun uu____8089  -> fun uu____8090  -> false)
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
        (fun uu____8104  ->
           let uu____8105 =
             FStar_Syntax_Syntax.gen_bv nm FStar_Pervasives_Native.None t  in
           ret uu____8105)
  
let (change : FStar_Reflection_Data.typ -> Prims.unit tac) =
  fun ty  ->
    let uu____8113 =
      mlog
        (fun uu____8118  ->
           let uu____8119 = FStar_Syntax_Print.term_to_string ty  in
           FStar_Util.print1 "change: ty = %s\n" uu____8119)
        (fun uu____8121  ->
           bind cur_goal
             (fun g  ->
                let uu____8125 = __tc g.FStar_Tactics_Types.context ty  in
                bind uu____8125
                  (fun uu____8145  ->
                     match uu____8145 with
                     | (ty1,uu____8155,guard) ->
                         let uu____8157 =
                           proc_guard "change" g.FStar_Tactics_Types.context
                             guard g.FStar_Tactics_Types.opts
                            in
                         bind uu____8157
                           (fun uu____8162  ->
                              let uu____8163 =
                                do_unify g.FStar_Tactics_Types.context
                                  g.FStar_Tactics_Types.goal_ty ty1
                                 in
                              bind uu____8163
                                (fun bb  ->
                                   if bb
                                   then
                                     replace_cur
                                       (let uu___126_8172 = g  in
                                        {
                                          FStar_Tactics_Types.context =
                                            (uu___126_8172.FStar_Tactics_Types.context);
                                          FStar_Tactics_Types.witness =
                                            (uu___126_8172.FStar_Tactics_Types.witness);
                                          FStar_Tactics_Types.goal_ty = ty1;
                                          FStar_Tactics_Types.opts =
                                            (uu___126_8172.FStar_Tactics_Types.opts);
                                          FStar_Tactics_Types.is_guard =
                                            (uu___126_8172.FStar_Tactics_Types.is_guard)
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
                                      let uu____8179 =
                                        do_unify
                                          g.FStar_Tactics_Types.context ng
                                          nty
                                         in
                                      bind uu____8179
                                        (fun b  ->
                                           if b
                                           then
                                             replace_cur
                                               (let uu___127_8188 = g  in
                                                {
                                                  FStar_Tactics_Types.context
                                                    =
                                                    (uu___127_8188.FStar_Tactics_Types.context);
                                                  FStar_Tactics_Types.witness
                                                    =
                                                    (uu___127_8188.FStar_Tactics_Types.witness);
                                                  FStar_Tactics_Types.goal_ty
                                                    = ty1;
                                                  FStar_Tactics_Types.opts =
                                                    (uu___127_8188.FStar_Tactics_Types.opts);
                                                  FStar_Tactics_Types.is_guard
                                                    =
                                                    (uu___127_8188.FStar_Tactics_Types.is_guard)
                                                })
                                           else fail "not convertible")))))))
       in
    FStar_All.pipe_left (wrap_err "change") uu____8113
  
let rec last : 'a . 'a Prims.list -> 'a =
  fun l  ->
    match l with
    | [] -> failwith "last: empty list"
    | x::[] -> x
    | uu____8207::xs -> last xs
  
let rec init : 'a . 'a Prims.list -> 'a Prims.list =
  fun l  ->
    match l with
    | [] -> failwith "init: empty list"
    | x::[] -> []
    | x::xs -> let uu____8232 = init xs  in x :: uu____8232
  
let rec (inspect :
  FStar_Syntax_Syntax.term -> FStar_Reflection_Data.term_view tac) =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t  in
    let t2 = FStar_Syntax_Util.un_uinst t1  in
    match t2.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_meta (t3,uu____8247) -> inspect t3
    | FStar_Syntax_Syntax.Tm_name bv ->
        FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_Var bv)
    | FStar_Syntax_Syntax.Tm_bvar bv ->
        FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_BVar bv)
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_FVar fv)
    | FStar_Syntax_Syntax.Tm_app (hd1,[]) ->
        failwith "inspect: empty arguments on Tm_app"
    | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
        let uu____8304 = last args  in
        (match uu____8304 with
         | (a,q) ->
             let q' = FStar_Reflection_Basic.inspect_aqual q  in
             let uu____8326 =
               let uu____8327 =
                 let uu____8332 =
                   let uu____8335 =
                     let uu____8336 = init args  in
                     FStar_Syntax_Syntax.mk_Tm_app hd1 uu____8336  in
                   uu____8335 FStar_Pervasives_Native.None
                     t2.FStar_Syntax_Syntax.pos
                    in
                 (uu____8332, (a, q'))  in
               FStar_Reflection_Data.Tv_App uu____8327  in
             FStar_All.pipe_left ret uu____8326)
    | FStar_Syntax_Syntax.Tm_abs ([],uu____8357,uu____8358) ->
        failwith "inspect: empty arguments on Tm_abs"
    | FStar_Syntax_Syntax.Tm_abs (bs,t3,k) ->
        let uu____8402 = FStar_Syntax_Subst.open_term bs t3  in
        (match uu____8402 with
         | (bs1,t4) ->
             (match bs1 with
              | [] -> failwith "impossible"
              | b::bs2 ->
                  let uu____8435 =
                    let uu____8436 =
                      let uu____8441 = FStar_Syntax_Util.abs bs2 t4 k  in
                      (b, uu____8441)  in
                    FStar_Reflection_Data.Tv_Abs uu____8436  in
                  FStar_All.pipe_left ret uu____8435))
    | FStar_Syntax_Syntax.Tm_type uu____8448 ->
        FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_Type ())
    | FStar_Syntax_Syntax.Tm_arrow ([],k) ->
        failwith "inspect: empty binders on arrow"
    | FStar_Syntax_Syntax.Tm_arrow uu____8468 ->
        let uu____8481 = FStar_Syntax_Util.arrow_one t2  in
        (match uu____8481 with
         | FStar_Pervasives_Native.Some (b,c) ->
             FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_Arrow (b, c))
         | FStar_Pervasives_Native.None  -> failwith "impossible")
    | FStar_Syntax_Syntax.Tm_refine (bv,t3) ->
        let b = FStar_Syntax_Syntax.mk_binder bv  in
        let uu____8511 = FStar_Syntax_Subst.open_term [b] t3  in
        (match uu____8511 with
         | (b',t4) ->
             let b1 =
               match b' with
               | b'1::[] -> b'1
               | uu____8542 -> failwith "impossible"  in
             FStar_All.pipe_left ret
               (FStar_Reflection_Data.Tv_Refine
                  ((FStar_Pervasives_Native.fst b1), t4)))
    | FStar_Syntax_Syntax.Tm_constant c ->
        let uu____8550 =
          let uu____8551 = FStar_Reflection_Basic.inspect_const c  in
          FStar_Reflection_Data.Tv_Const uu____8551  in
        FStar_All.pipe_left ret uu____8550
    | FStar_Syntax_Syntax.Tm_uvar (u,t3) ->
        let uu____8580 =
          let uu____8581 =
            let uu____8586 =
              let uu____8587 = FStar_Syntax_Unionfind.uvar_id u  in
              FStar_BigInt.of_int_fs uu____8587  in
            (uu____8586, t3)  in
          FStar_Reflection_Data.Tv_Uvar uu____8581  in
        FStar_All.pipe_left ret uu____8580
    | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),t21) ->
        if lb.FStar_Syntax_Syntax.lbunivs <> []
        then FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
        else
          (match lb.FStar_Syntax_Syntax.lbname with
           | FStar_Util.Inr uu____8615 ->
               FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
           | FStar_Util.Inl bv ->
               let b = FStar_Syntax_Syntax.mk_binder bv  in
               let uu____8620 = FStar_Syntax_Subst.open_term [b] t21  in
               (match uu____8620 with
                | (bs,t22) ->
                    let b1 =
                      match bs with
                      | b1::[] -> b1
                      | uu____8651 ->
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
           | FStar_Util.Inr uu____8683 ->
               FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
           | FStar_Util.Inl bv ->
               let uu____8687 = FStar_Syntax_Subst.open_let_rec [lb] t21  in
               (match uu____8687 with
                | (lbs,t22) ->
                    (match lbs with
                     | lb1::[] ->
                         (match lb1.FStar_Syntax_Syntax.lbname with
                          | FStar_Util.Inr uu____8707 ->
                              ret FStar_Reflection_Data.Tv_Unknown
                          | FStar_Util.Inl bv1 ->
                              FStar_All.pipe_left ret
                                (FStar_Reflection_Data.Tv_Let
                                   (true, bv1,
                                     (lb1.FStar_Syntax_Syntax.lbdef), t22)))
                     | uu____8713 ->
                         failwith
                           "impossible: open_term returned different amount of binders")))
    | FStar_Syntax_Syntax.Tm_match (t3,brs) ->
        let rec inspect_pat p =
          match p.FStar_Syntax_Syntax.v with
          | FStar_Syntax_Syntax.Pat_constant c ->
              let uu____8765 = FStar_Reflection_Basic.inspect_const c  in
              FStar_Reflection_Data.Pat_Constant uu____8765
          | FStar_Syntax_Syntax.Pat_cons (fv,ps) ->
              let uu____8784 =
                let uu____8791 =
                  FStar_List.map
                    (fun uu____8803  ->
                       match uu____8803 with
                       | (p1,uu____8811) -> inspect_pat p1) ps
                   in
                (fv, uu____8791)  in
              FStar_Reflection_Data.Pat_Cons uu____8784
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
            (fun uu___61_8865  ->
               match uu___61_8865 with
               | (pat,uu____8887,t4) ->
                   let uu____8905 = inspect_pat pat  in (uu____8905, t4))
            brs1
           in
        FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_Match (t3, brs2))
    | FStar_Syntax_Syntax.Tm_unknown  ->
        FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
    | uu____8922 ->
        ((let uu____8924 =
            let uu____8929 =
              let uu____8930 = FStar_Syntax_Print.tag_of_term t2  in
              let uu____8931 = FStar_Syntax_Print.term_to_string t2  in
              FStar_Util.format2
                "inspect: outside of expected syntax (%s, %s)\n" uu____8930
                uu____8931
               in
            (FStar_Errors.Warning_CantInspect, uu____8929)  in
          FStar_Errors.log_issue t2.FStar_Syntax_Syntax.pos uu____8924);
         FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown)
  
let (pack : FStar_Reflection_Data.term_view -> FStar_Syntax_Syntax.term tac)
  =
  fun tv  ->
    match tv with
    | FStar_Reflection_Data.Tv_Var bv ->
        let uu____8942 = FStar_Syntax_Syntax.bv_to_name bv  in
        FStar_All.pipe_left ret uu____8942
    | FStar_Reflection_Data.Tv_BVar bv ->
        let uu____8946 = FStar_Syntax_Syntax.bv_to_tm bv  in
        FStar_All.pipe_left ret uu____8946
    | FStar_Reflection_Data.Tv_FVar fv ->
        let uu____8950 = FStar_Syntax_Syntax.fv_to_tm fv  in
        FStar_All.pipe_left ret uu____8950
    | FStar_Reflection_Data.Tv_App (l,(r,q)) ->
        let q' = FStar_Reflection_Basic.pack_aqual q  in
        let uu____8961 = FStar_Syntax_Util.mk_app l [(r, q')]  in
        FStar_All.pipe_left ret uu____8961
    | FStar_Reflection_Data.Tv_Abs (b,t) ->
        let uu____8982 =
          FStar_Syntax_Util.abs [b] t FStar_Pervasives_Native.None  in
        FStar_All.pipe_left ret uu____8982
    | FStar_Reflection_Data.Tv_Arrow (b,c) ->
        let uu____8987 = FStar_Syntax_Util.arrow [b] c  in
        FStar_All.pipe_left ret uu____8987
    | FStar_Reflection_Data.Tv_Type () ->
        FStar_All.pipe_left ret FStar_Syntax_Util.ktype
    | FStar_Reflection_Data.Tv_Refine (bv,t) ->
        let uu____9008 = FStar_Syntax_Util.refine bv t  in
        FStar_All.pipe_left ret uu____9008
    | FStar_Reflection_Data.Tv_Const c ->
        let uu____9020 =
          let uu____9023 =
            let uu____9026 =
              let uu____9027 = FStar_Reflection_Basic.pack_const c  in
              FStar_Syntax_Syntax.Tm_constant uu____9027  in
            FStar_Syntax_Syntax.mk uu____9026  in
          uu____9023 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
        FStar_All.pipe_left ret uu____9020
    | FStar_Reflection_Data.Tv_Uvar (u,t) ->
        let uu____9041 =
          let uu____9044 = FStar_BigInt.to_int_fs u  in
          FStar_Syntax_Util.uvar_from_id uu____9044 t  in
        FStar_All.pipe_left ret uu____9041
    | FStar_Reflection_Data.Tv_Let (false ,bv,t1,t2) ->
        let lb =
          FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl bv) []
            bv.FStar_Syntax_Syntax.sort FStar_Parser_Const.effect_Tot_lid t1
            [] FStar_Range.dummyRange
           in
        let uu____9059 =
          let uu____9062 =
            let uu____9065 =
              let uu____9066 =
                let uu____9079 =
                  let uu____9080 =
                    let uu____9081 = FStar_Syntax_Syntax.mk_binder bv  in
                    [uu____9081]  in
                  FStar_Syntax_Subst.close uu____9080 t2  in
                ((false, [lb]), uu____9079)  in
              FStar_Syntax_Syntax.Tm_let uu____9066  in
            FStar_Syntax_Syntax.mk uu____9065  in
          uu____9062 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
        FStar_All.pipe_left ret uu____9059
    | FStar_Reflection_Data.Tv_Let (true ,bv,t1,t2) ->
        let lb =
          FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl bv) []
            bv.FStar_Syntax_Syntax.sort FStar_Parser_Const.effect_Tot_lid t1
            [] FStar_Range.dummyRange
           in
        let uu____9107 = FStar_Syntax_Subst.open_let_rec [lb] t2  in
        (match uu____9107 with
         | (lbs_open,body_open) ->
             let uu____9122 = FStar_Syntax_Subst.close_let_rec [lb] body_open
                in
             (match uu____9122 with
              | (lbs,body) ->
                  let uu____9137 =
                    FStar_Syntax_Syntax.mk
                      (FStar_Syntax_Syntax.Tm_let ((true, lbs), body))
                      FStar_Pervasives_Native.None FStar_Range.dummyRange
                     in
                  FStar_All.pipe_left ret uu____9137))
    | FStar_Reflection_Data.Tv_Match (t,brs) ->
        let wrap v1 =
          {
            FStar_Syntax_Syntax.v = v1;
            FStar_Syntax_Syntax.p = FStar_Range.dummyRange
          }  in
        let rec pack_pat p =
          match p with
          | FStar_Reflection_Data.Pat_Constant c ->
              let uu____9173 =
                let uu____9174 = FStar_Reflection_Basic.pack_const c  in
                FStar_Syntax_Syntax.Pat_constant uu____9174  in
              FStar_All.pipe_left wrap uu____9173
          | FStar_Reflection_Data.Pat_Cons (fv,ps) ->
              let uu____9183 =
                let uu____9184 =
                  let uu____9197 =
                    FStar_List.map
                      (fun p1  ->
                         let uu____9211 = pack_pat p1  in (uu____9211, false))
                      ps
                     in
                  (fv, uu____9197)  in
                FStar_Syntax_Syntax.Pat_cons uu____9184  in
              FStar_All.pipe_left wrap uu____9183
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
            (fun uu___62_9261  ->
               match uu___62_9261 with
               | (pat,t1) ->
                   let uu____9278 = pack_pat pat  in
                   (uu____9278, FStar_Pervasives_Native.None, t1)) brs
           in
        let brs2 = FStar_List.map FStar_Syntax_Subst.close_branch brs1  in
        let uu____9288 =
          FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_match (t, brs2))
            FStar_Pervasives_Native.None FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____9288
    | FStar_Reflection_Data.Tv_AscribedT (e,t,tacopt) ->
        let uu____9308 =
          FStar_Syntax_Syntax.mk
            (FStar_Syntax_Syntax.Tm_ascribed
               (e, ((FStar_Util.Inl t), tacopt),
                 FStar_Pervasives_Native.None)) FStar_Pervasives_Native.None
            FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____9308
    | FStar_Reflection_Data.Tv_AscribedC (e,c,tacopt) ->
        let uu____9350 =
          FStar_Syntax_Syntax.mk
            (FStar_Syntax_Syntax.Tm_ascribed
               (e, ((FStar_Util.Inr c), tacopt),
                 FStar_Pervasives_Native.None)) FStar_Pervasives_Native.None
            FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____9350
    | FStar_Reflection_Data.Tv_Unknown  ->
        let uu____9385 =
          FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
            FStar_Pervasives_Native.None FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____9385
  
let (goal_of_goal_ty :
  env ->
    FStar_Reflection_Data.typ ->
      (FStar_Tactics_Types.goal,FStar_TypeChecker_Env.guard_t)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun typ  ->
      let uu____9410 =
        FStar_TypeChecker_Util.new_implicit_var "proofstate_of_goal_ty"
          typ.FStar_Syntax_Syntax.pos env typ
         in
      match uu____9410 with
      | (u,uu____9428,g_u) ->
          let g =
            let uu____9443 = FStar_Options.peek ()  in
            {
              FStar_Tactics_Types.context = env;
              FStar_Tactics_Types.witness = u;
              FStar_Tactics_Types.goal_ty = typ;
              FStar_Tactics_Types.opts = uu____9443;
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
      let uu____9454 = goal_of_goal_ty env typ  in
      match uu____9454 with
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
  