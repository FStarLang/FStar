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
  
let (dismiss : Prims.unit -> Prims.unit tac) =
  fun uu____1112  ->
    bind get
      (fun p  ->
         match p.FStar_Tactics_Types.goals with
         | [] -> fail "dismiss: no more goals"
         | uu____1119 -> __dismiss)
  
let (solve :
  FStar_Tactics_Types.goal -> FStar_Syntax_Syntax.term -> Prims.unit tac) =
  fun goal  ->
    fun solution  ->
      let uu____1132 = trysolve goal solution  in
      bind uu____1132
        (fun b  ->
           if b
           then __dismiss
           else
             (let uu____1140 =
                let uu____1141 =
                  tts goal.FStar_Tactics_Types.context solution  in
                let uu____1142 =
                  tts goal.FStar_Tactics_Types.context
                    goal.FStar_Tactics_Types.witness
                   in
                let uu____1143 =
                  tts goal.FStar_Tactics_Types.context
                    goal.FStar_Tactics_Types.goal_ty
                   in
                FStar_Util.format3 "%s does not solve %s : %s" uu____1141
                  uu____1142 uu____1143
                 in
              fail uu____1140))
  
let (dismiss_all : Prims.unit tac) =
  bind get
    (fun p  ->
       set
         (let uu___69_1150 = p  in
          {
            FStar_Tactics_Types.main_context =
              (uu___69_1150.FStar_Tactics_Types.main_context);
            FStar_Tactics_Types.main_goal =
              (uu___69_1150.FStar_Tactics_Types.main_goal);
            FStar_Tactics_Types.all_implicits =
              (uu___69_1150.FStar_Tactics_Types.all_implicits);
            FStar_Tactics_Types.goals = [];
            FStar_Tactics_Types.smt_goals =
              (uu___69_1150.FStar_Tactics_Types.smt_goals);
            FStar_Tactics_Types.depth =
              (uu___69_1150.FStar_Tactics_Types.depth);
            FStar_Tactics_Types.__dump =
              (uu___69_1150.FStar_Tactics_Types.__dump);
            FStar_Tactics_Types.psc = (uu___69_1150.FStar_Tactics_Types.psc);
            FStar_Tactics_Types.entry_range =
              (uu___69_1150.FStar_Tactics_Types.entry_range);
            FStar_Tactics_Types.guard_policy =
              (uu___69_1150.FStar_Tactics_Types.guard_policy);
            FStar_Tactics_Types.freshness =
              (uu___69_1150.FStar_Tactics_Types.freshness)
          }))
  
let (nwarn : Prims.int FStar_ST.ref) =
  FStar_Util.mk_ref (Prims.parse_int "0") 
let (check_valid_goal : FStar_Tactics_Types.goal -> Prims.unit) =
  fun g  ->
    let uu____1167 = FStar_Options.defensive ()  in
    if uu____1167
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
        let uu____1179 = FStar_TypeChecker_Env.pop_bv e  in
        match uu____1179 with
        | FStar_Pervasives_Native.None  -> b3
        | FStar_Pervasives_Native.Some (bv,e1) ->
            let b4 =
              b3 &&
                (FStar_TypeChecker_Env.closed e1 bv.FStar_Syntax_Syntax.sort)
               in
            aux b4 e1
         in
      let uu____1197 =
        (let uu____1200 = aux b2 env  in Prims.op_Negation uu____1200) &&
          (let uu____1202 = FStar_ST.op_Bang nwarn  in
           uu____1202 < (Prims.parse_int "5"))
         in
      (if uu____1197
       then
         ((let uu____1223 =
             let uu____1228 =
               let uu____1229 = goal_to_string g  in
               FStar_Util.format1
                 "The following goal is ill-formed. Keeping calm and carrying on...\n<%s>\n\n"
                 uu____1229
                in
             (FStar_Errors.Warning_IllFormedGoal, uu____1228)  in
           FStar_Errors.log_issue
             (g.FStar_Tactics_Types.goal_ty).FStar_Syntax_Syntax.pos
             uu____1223);
          (let uu____1230 =
             let uu____1231 = FStar_ST.op_Bang nwarn  in
             uu____1231 + (Prims.parse_int "1")  in
           FStar_ST.op_Colon_Equals nwarn uu____1230))
       else ())
    else ()
  
let (add_goals : FStar_Tactics_Types.goal Prims.list -> Prims.unit tac) =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___70_1289 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___70_1289.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___70_1289.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___70_1289.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (FStar_List.append gs p.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___70_1289.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___70_1289.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___70_1289.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___70_1289.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___70_1289.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___70_1289.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___70_1289.FStar_Tactics_Types.freshness)
            }))
  
let (add_smt_goals : FStar_Tactics_Types.goal Prims.list -> Prims.unit tac) =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___71_1307 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___71_1307.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___71_1307.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___71_1307.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___71_1307.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (FStar_List.append gs p.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___71_1307.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___71_1307.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___71_1307.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___71_1307.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___71_1307.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___71_1307.FStar_Tactics_Types.freshness)
            }))
  
let (push_goals : FStar_Tactics_Types.goal Prims.list -> Prims.unit tac) =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___72_1325 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___72_1325.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___72_1325.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___72_1325.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (FStar_List.append p.FStar_Tactics_Types.goals gs);
              FStar_Tactics_Types.smt_goals =
                (uu___72_1325.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___72_1325.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___72_1325.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___72_1325.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___72_1325.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___72_1325.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___72_1325.FStar_Tactics_Types.freshness)
            }))
  
let (push_smt_goals : FStar_Tactics_Types.goal Prims.list -> Prims.unit tac)
  =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___73_1343 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___73_1343.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___73_1343.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___73_1343.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___73_1343.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (FStar_List.append p.FStar_Tactics_Types.smt_goals gs);
              FStar_Tactics_Types.depth =
                (uu___73_1343.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___73_1343.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___73_1343.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___73_1343.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___73_1343.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___73_1343.FStar_Tactics_Types.freshness)
            }))
  
let (replace_cur : FStar_Tactics_Types.goal -> Prims.unit tac) =
  fun g  -> bind __dismiss (fun uu____1352  -> add_goals [g]) 
let (add_implicits : implicits -> Prims.unit tac) =
  fun i  ->
    bind get
      (fun p  ->
         set
           (let uu___74_1364 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___74_1364.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___74_1364.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (FStar_List.append i p.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___74_1364.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___74_1364.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___74_1364.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___74_1364.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___74_1364.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___74_1364.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___74_1364.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___74_1364.FStar_Tactics_Types.freshness)
            }))
  
let (new_uvar :
  Prims.string ->
    env -> FStar_Reflection_Data.typ -> FStar_Syntax_Syntax.term tac)
  =
  fun reason  ->
    fun env  ->
      fun typ  ->
        let uu____1390 =
          FStar_TypeChecker_Util.new_implicit_var reason
            typ.FStar_Syntax_Syntax.pos env typ
           in
        match uu____1390 with
        | (u,uu____1406,g_u) ->
            let uu____1420 =
              add_implicits g_u.FStar_TypeChecker_Env.implicits  in
            bind uu____1420 (fun uu____1424  -> ret u)
  
let (is_true : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____1428 = FStar_Syntax_Util.un_squash t  in
    match uu____1428 with
    | FStar_Pervasives_Native.Some t' ->
        let uu____1438 =
          let uu____1439 = FStar_Syntax_Subst.compress t'  in
          uu____1439.FStar_Syntax_Syntax.n  in
        (match uu____1438 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.true_lid
         | uu____1443 -> false)
    | uu____1444 -> false
  
let (is_false : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____1452 = FStar_Syntax_Util.un_squash t  in
    match uu____1452 with
    | FStar_Pervasives_Native.Some t' ->
        let uu____1462 =
          let uu____1463 = FStar_Syntax_Subst.compress t'  in
          uu____1463.FStar_Syntax_Syntax.n  in
        (match uu____1462 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.false_lid
         | uu____1467 -> false)
    | uu____1468 -> false
  
let (cur_goal : Prims.unit -> FStar_Tactics_Types.goal tac) =
  fun uu____1477  ->
    bind get
      (fun p  ->
         match p.FStar_Tactics_Types.goals with
         | [] -> fail "No more goals (1)"
         | hd1::tl1 -> ret hd1)
  
let (tadmit : Prims.unit -> Prims.unit tac) =
  fun uu____1492  ->
    let uu____1495 =
      let uu____1498 = cur_goal ()  in
      bind uu____1498
        (fun g  ->
           (let uu____1505 =
              let uu____1510 =
                let uu____1511 = goal_to_string g  in
                FStar_Util.format1 "Tactics admitted goal <%s>\n\n"
                  uu____1511
                 in
              (FStar_Errors.Warning_TacAdmit, uu____1510)  in
            FStar_Errors.log_issue
              (g.FStar_Tactics_Types.goal_ty).FStar_Syntax_Syntax.pos
              uu____1505);
           solve g FStar_Syntax_Util.exp_unit)
       in
    FStar_All.pipe_left (wrap_err "tadmit") uu____1495
  
let (fresh : Prims.unit -> FStar_BigInt.t tac) =
  fun uu____1520  ->
    bind get
      (fun ps  ->
         let n1 = ps.FStar_Tactics_Types.freshness  in
         let ps1 =
           let uu___75_1530 = ps  in
           {
             FStar_Tactics_Types.main_context =
               (uu___75_1530.FStar_Tactics_Types.main_context);
             FStar_Tactics_Types.main_goal =
               (uu___75_1530.FStar_Tactics_Types.main_goal);
             FStar_Tactics_Types.all_implicits =
               (uu___75_1530.FStar_Tactics_Types.all_implicits);
             FStar_Tactics_Types.goals =
               (uu___75_1530.FStar_Tactics_Types.goals);
             FStar_Tactics_Types.smt_goals =
               (uu___75_1530.FStar_Tactics_Types.smt_goals);
             FStar_Tactics_Types.depth =
               (uu___75_1530.FStar_Tactics_Types.depth);
             FStar_Tactics_Types.__dump =
               (uu___75_1530.FStar_Tactics_Types.__dump);
             FStar_Tactics_Types.psc = (uu___75_1530.FStar_Tactics_Types.psc);
             FStar_Tactics_Types.entry_range =
               (uu___75_1530.FStar_Tactics_Types.entry_range);
             FStar_Tactics_Types.guard_policy =
               (uu___75_1530.FStar_Tactics_Types.guard_policy);
             FStar_Tactics_Types.freshness = (n1 + (Prims.parse_int "1"))
           }  in
         let uu____1531 = set ps1  in
         bind uu____1531
           (fun uu____1536  ->
              let uu____1537 = FStar_BigInt.of_int_fs n1  in ret uu____1537))
  
let (ngoals : Prims.unit -> FStar_BigInt.t tac) =
  fun uu____1542  ->
    bind get
      (fun ps  ->
         let n1 = FStar_List.length ps.FStar_Tactics_Types.goals  in
         let uu____1550 = FStar_BigInt.of_int_fs n1  in ret uu____1550)
  
let (ngoals_smt : Prims.unit -> FStar_BigInt.t tac) =
  fun uu____1561  ->
    bind get
      (fun ps  ->
         let n1 = FStar_List.length ps.FStar_Tactics_Types.smt_goals  in
         let uu____1569 = FStar_BigInt.of_int_fs n1  in ret uu____1569)
  
let (is_guard : Prims.unit -> Prims.bool tac) =
  fun uu____1580  ->
    let uu____1583 = cur_goal ()  in
    bind uu____1583 (fun g  -> ret g.FStar_Tactics_Types.is_guard)
  
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
            let uu____1607 = env.FStar_TypeChecker_Env.universe_of env phi
               in
            FStar_Syntax_Util.mk_squash uu____1607 phi  in
          let uu____1608 = new_uvar reason env typ  in
          bind uu____1608
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
             (fun uu____1653  ->
                let uu____1654 = tts e t  in
                FStar_Util.print1 "Tac> __tc(%s)\n" uu____1654)
             (fun uu____1656  ->
                try
                  let uu____1676 =
                    (ps.FStar_Tactics_Types.main_context).FStar_TypeChecker_Env.type_of
                      e t
                     in
                  ret uu____1676
                with
                | FStar_Errors.Err (uu____1703,msg) ->
                    let uu____1705 = tts e t  in
                    let uu____1706 =
                      let uu____1707 = FStar_TypeChecker_Env.all_binders e
                         in
                      FStar_All.pipe_right uu____1707
                        (FStar_Syntax_Print.binders_to_string ", ")
                       in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____1705 uu____1706 msg
                | FStar_Errors.Error (uu____1714,msg,uu____1716) ->
                    let uu____1717 = tts e t  in
                    let uu____1718 =
                      let uu____1719 = FStar_TypeChecker_Env.all_binders e
                         in
                      FStar_All.pipe_right uu____1719
                        (FStar_Syntax_Print.binders_to_string ", ")
                       in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____1717 uu____1718 msg))
  
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
  
let (get_guard_policy : Prims.unit -> FStar_Tactics_Types.guard_policy tac) =
  fun uu____1740  ->
    bind get (fun ps  -> ret ps.FStar_Tactics_Types.guard_policy)
  
let (set_guard_policy : FStar_Tactics_Types.guard_policy -> Prims.unit tac) =
  fun pol  ->
    bind get
      (fun ps  ->
         set
           (let uu___78_1756 = ps  in
            {
              FStar_Tactics_Types.main_context =
                (uu___78_1756.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___78_1756.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___78_1756.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___78_1756.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___78_1756.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___78_1756.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___78_1756.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___78_1756.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___78_1756.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy = pol;
              FStar_Tactics_Types.freshness =
                (uu___78_1756.FStar_Tactics_Types.freshness)
            }))
  
let with_policy : 'a . FStar_Tactics_Types.guard_policy -> 'a tac -> 'a tac =
  fun pol  ->
    fun t  ->
      let uu____1775 = get_guard_policy ()  in
      bind uu____1775
        (fun old_pol  ->
           let uu____1781 = set_guard_policy pol  in
           bind uu____1781
             (fun uu____1785  ->
                bind t
                  (fun r  ->
                     let uu____1789 = set_guard_policy old_pol  in
                     bind uu____1789 (fun uu____1793  -> ret r))))
  
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
          let uu____1810 =
            let uu____1811 = FStar_TypeChecker_Rel.simplify_guard e g  in
            uu____1811.FStar_TypeChecker_Env.guard_f  in
          match uu____1810 with
          | FStar_TypeChecker_Common.Trivial  -> ret ()
          | FStar_TypeChecker_Common.NonTrivial f ->
              let uu____1815 = istrivial e f  in
              if uu____1815
              then ret ()
              else
                bind get
                  (fun ps  ->
                     match ps.FStar_Tactics_Types.guard_policy with
                     | FStar_Tactics_Types.Drop  -> ret ()
                     | FStar_Tactics_Types.Goal  ->
                         let uu____1823 = mk_irrelevant_goal reason e f opts
                            in
                         bind uu____1823
                           (fun goal  ->
                              let goal1 =
                                let uu___79_1830 = goal  in
                                {
                                  FStar_Tactics_Types.context =
                                    (uu___79_1830.FStar_Tactics_Types.context);
                                  FStar_Tactics_Types.witness =
                                    (uu___79_1830.FStar_Tactics_Types.witness);
                                  FStar_Tactics_Types.goal_ty =
                                    (uu___79_1830.FStar_Tactics_Types.goal_ty);
                                  FStar_Tactics_Types.opts =
                                    (uu___79_1830.FStar_Tactics_Types.opts);
                                  FStar_Tactics_Types.is_guard = true
                                }  in
                              push_goals [goal1])
                     | FStar_Tactics_Types.SMT  ->
                         let uu____1831 = mk_irrelevant_goal reason e f opts
                            in
                         bind uu____1831
                           (fun goal  ->
                              let goal1 =
                                let uu___80_1838 = goal  in
                                {
                                  FStar_Tactics_Types.context =
                                    (uu___80_1838.FStar_Tactics_Types.context);
                                  FStar_Tactics_Types.witness =
                                    (uu___80_1838.FStar_Tactics_Types.witness);
                                  FStar_Tactics_Types.goal_ty =
                                    (uu___80_1838.FStar_Tactics_Types.goal_ty);
                                  FStar_Tactics_Types.opts =
                                    (uu___80_1838.FStar_Tactics_Types.opts);
                                  FStar_Tactics_Types.is_guard = true
                                }  in
                              push_smt_goals [goal1])
                     | FStar_Tactics_Types.Force  ->
                         (try
                            let uu____1846 =
                              let uu____1847 =
                                let uu____1848 =
                                  FStar_TypeChecker_Rel.discharge_guard_no_smt
                                    e g
                                   in
                                FStar_All.pipe_left
                                  FStar_TypeChecker_Rel.is_trivial uu____1848
                                 in
                              Prims.op_Negation uu____1847  in
                            if uu____1846
                            then
                              mlog
                                (fun uu____1853  ->
                                   let uu____1854 =
                                     FStar_TypeChecker_Rel.guard_to_string e
                                       g
                                      in
                                   FStar_Util.print1 "guard = %s\n"
                                     uu____1854)
                                (fun uu____1856  ->
                                   fail1 "Forcing the guard failed %s)"
                                     reason)
                            else ret ()
                          with
                          | uu____1863 ->
                              mlog
                                (fun uu____1866  ->
                                   let uu____1867 =
                                     FStar_TypeChecker_Rel.guard_to_string e
                                       g
                                      in
                                   FStar_Util.print1 "guard = %s\n"
                                     uu____1867)
                                (fun uu____1869  ->
                                   fail1 "Forcing the guard failed (%s)"
                                     reason)))
  
let (tc : FStar_Syntax_Syntax.term -> FStar_Reflection_Data.typ tac) =
  fun t  ->
    let uu____1877 =
      let uu____1880 = cur_goal ()  in
      bind uu____1880
        (fun goal  ->
           let uu____1886 = __tc goal.FStar_Tactics_Types.context t  in
           bind uu____1886
             (fun uu____1906  ->
                match uu____1906 with
                | (t1,typ,guard) ->
                    let uu____1918 =
                      proc_guard "tc" goal.FStar_Tactics_Types.context guard
                        goal.FStar_Tactics_Types.opts
                       in
                    bind uu____1918 (fun uu____1922  -> ret typ)))
       in
    FStar_All.pipe_left (wrap_err "tc") uu____1877
  
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
          let uu____1943 = mk_irrelevant_goal reason env phi opts  in
          bind uu____1943 (fun goal  -> add_goals [goal])
  
let (trivial : Prims.unit -> Prims.unit tac) =
  fun uu____1952  ->
    let uu____1955 = cur_goal ()  in
    bind uu____1955
      (fun goal  ->
         let uu____1961 =
           istrivial goal.FStar_Tactics_Types.context
             goal.FStar_Tactics_Types.goal_ty
            in
         if uu____1961
         then solve goal FStar_Syntax_Util.exp_unit
         else
           (let uu____1965 =
              tts goal.FStar_Tactics_Types.context
                goal.FStar_Tactics_Types.goal_ty
               in
            fail1 "Not a trivial goal: %s" uu____1965))
  
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
          let uu____1986 =
            let uu____1987 = FStar_TypeChecker_Rel.simplify_guard e g  in
            uu____1987.FStar_TypeChecker_Env.guard_f  in
          match uu____1986 with
          | FStar_TypeChecker_Common.Trivial  ->
              ret FStar_Pervasives_Native.None
          | FStar_TypeChecker_Common.NonTrivial f ->
              let uu____1995 = istrivial e f  in
              if uu____1995
              then ret FStar_Pervasives_Native.None
              else
                (let uu____2003 = mk_irrelevant_goal reason e f opts  in
                 bind uu____2003
                   (fun goal  ->
                      ret
                        (FStar_Pervasives_Native.Some
                           (let uu___83_2013 = goal  in
                            {
                              FStar_Tactics_Types.context =
                                (uu___83_2013.FStar_Tactics_Types.context);
                              FStar_Tactics_Types.witness =
                                (uu___83_2013.FStar_Tactics_Types.witness);
                              FStar_Tactics_Types.goal_ty =
                                (uu___83_2013.FStar_Tactics_Types.goal_ty);
                              FStar_Tactics_Types.opts =
                                (uu___83_2013.FStar_Tactics_Types.opts);
                              FStar_Tactics_Types.is_guard = true
                            }))))
  
let (smt : Prims.unit -> Prims.unit tac) =
  fun uu____2018  ->
    let uu____2021 = cur_goal ()  in
    bind uu____2021
      (fun g  ->
         let uu____2027 = is_irrelevant g  in
         if uu____2027
         then bind __dismiss (fun uu____2031  -> add_smt_goals [g])
         else
           (let uu____2033 =
              tts g.FStar_Tactics_Types.context g.FStar_Tactics_Types.goal_ty
               in
            fail1 "goal is not irrelevant: cannot dispatch to smt (%s)"
              uu____2033))
  
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
             let uu____2074 =
               try
                 let uu____2108 =
                   let uu____2117 = FStar_BigInt.to_int_fs n1  in
                   FStar_List.splitAt uu____2117 p.FStar_Tactics_Types.goals
                    in
                 ret uu____2108
               with | uu____2139 -> fail "divide: not enough goals"  in
             bind uu____2074
               (fun uu____2166  ->
                  match uu____2166 with
                  | (lgs,rgs) ->
                      let lp =
                        let uu___84_2192 = p  in
                        {
                          FStar_Tactics_Types.main_context =
                            (uu___84_2192.FStar_Tactics_Types.main_context);
                          FStar_Tactics_Types.main_goal =
                            (uu___84_2192.FStar_Tactics_Types.main_goal);
                          FStar_Tactics_Types.all_implicits =
                            (uu___84_2192.FStar_Tactics_Types.all_implicits);
                          FStar_Tactics_Types.goals = lgs;
                          FStar_Tactics_Types.smt_goals = [];
                          FStar_Tactics_Types.depth =
                            (uu___84_2192.FStar_Tactics_Types.depth);
                          FStar_Tactics_Types.__dump =
                            (uu___84_2192.FStar_Tactics_Types.__dump);
                          FStar_Tactics_Types.psc =
                            (uu___84_2192.FStar_Tactics_Types.psc);
                          FStar_Tactics_Types.entry_range =
                            (uu___84_2192.FStar_Tactics_Types.entry_range);
                          FStar_Tactics_Types.guard_policy =
                            (uu___84_2192.FStar_Tactics_Types.guard_policy);
                          FStar_Tactics_Types.freshness =
                            (uu___84_2192.FStar_Tactics_Types.freshness)
                        }  in
                      let rp =
                        let uu___85_2194 = p  in
                        {
                          FStar_Tactics_Types.main_context =
                            (uu___85_2194.FStar_Tactics_Types.main_context);
                          FStar_Tactics_Types.main_goal =
                            (uu___85_2194.FStar_Tactics_Types.main_goal);
                          FStar_Tactics_Types.all_implicits =
                            (uu___85_2194.FStar_Tactics_Types.all_implicits);
                          FStar_Tactics_Types.goals = rgs;
                          FStar_Tactics_Types.smt_goals = [];
                          FStar_Tactics_Types.depth =
                            (uu___85_2194.FStar_Tactics_Types.depth);
                          FStar_Tactics_Types.__dump =
                            (uu___85_2194.FStar_Tactics_Types.__dump);
                          FStar_Tactics_Types.psc =
                            (uu___85_2194.FStar_Tactics_Types.psc);
                          FStar_Tactics_Types.entry_range =
                            (uu___85_2194.FStar_Tactics_Types.entry_range);
                          FStar_Tactics_Types.guard_policy =
                            (uu___85_2194.FStar_Tactics_Types.guard_policy);
                          FStar_Tactics_Types.freshness =
                            (uu___85_2194.FStar_Tactics_Types.freshness)
                        }  in
                      let uu____2195 = set lp  in
                      bind uu____2195
                        (fun uu____2203  ->
                           bind l
                             (fun a  ->
                                bind get
                                  (fun lp'  ->
                                     let uu____2217 = set rp  in
                                     bind uu____2217
                                       (fun uu____2225  ->
                                          bind r
                                            (fun b  ->
                                               bind get
                                                 (fun rp'  ->
                                                    let p' =
                                                      let uu___86_2241 = p
                                                         in
                                                      {
                                                        FStar_Tactics_Types.main_context
                                                          =
                                                          (uu___86_2241.FStar_Tactics_Types.main_context);
                                                        FStar_Tactics_Types.main_goal
                                                          =
                                                          (uu___86_2241.FStar_Tactics_Types.main_goal);
                                                        FStar_Tactics_Types.all_implicits
                                                          =
                                                          (uu___86_2241.FStar_Tactics_Types.all_implicits);
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
                                                          (uu___86_2241.FStar_Tactics_Types.depth);
                                                        FStar_Tactics_Types.__dump
                                                          =
                                                          (uu___86_2241.FStar_Tactics_Types.__dump);
                                                        FStar_Tactics_Types.psc
                                                          =
                                                          (uu___86_2241.FStar_Tactics_Types.psc);
                                                        FStar_Tactics_Types.entry_range
                                                          =
                                                          (uu___86_2241.FStar_Tactics_Types.entry_range);
                                                        FStar_Tactics_Types.guard_policy
                                                          =
                                                          (uu___86_2241.FStar_Tactics_Types.guard_policy);
                                                        FStar_Tactics_Types.freshness
                                                          =
                                                          (uu___86_2241.FStar_Tactics_Types.freshness)
                                                      }  in
                                                    let uu____2242 = set p'
                                                       in
                                                    bind uu____2242
                                                      (fun uu____2250  ->
                                                         ret (a, b))))))))))
  
let focus : 'a . 'a tac -> 'a tac =
  fun f  ->
    let uu____2268 = divide FStar_BigInt.one f idtac  in
    bind uu____2268
      (fun uu____2281  -> match uu____2281 with | (a,()) -> ret a)
  
let rec map : 'a . 'a tac -> 'a Prims.list tac =
  fun tau  ->
    bind get
      (fun p  ->
         match p.FStar_Tactics_Types.goals with
         | [] -> ret []
         | uu____2315::uu____2316 ->
             let uu____2319 =
               let uu____2328 = map tau  in
               divide FStar_BigInt.one tau uu____2328  in
             bind uu____2319
               (fun uu____2346  ->
                  match uu____2346 with | (h,t) -> ret (h :: t)))
  
let (seq : Prims.unit tac -> Prims.unit tac -> Prims.unit tac) =
  fun t1  ->
    fun t2  ->
      let uu____2383 =
        bind t1
          (fun uu____2388  ->
             let uu____2389 = map t2  in
             bind uu____2389 (fun uu____2397  -> ret ()))
         in
      focus uu____2383
  
let (intro : Prims.unit -> FStar_Syntax_Syntax.binder tac) =
  fun uu____2404  ->
    let uu____2407 =
      let uu____2410 = cur_goal ()  in
      bind uu____2410
        (fun goal  ->
           let uu____2419 =
             FStar_Syntax_Util.arrow_one goal.FStar_Tactics_Types.goal_ty  in
           match uu____2419 with
           | FStar_Pervasives_Native.Some (b,c) ->
               let uu____2434 =
                 let uu____2435 = FStar_Syntax_Util.is_total_comp c  in
                 Prims.op_Negation uu____2435  in
               if uu____2434
               then fail "Codomain is effectful"
               else
                 (let env' =
                    FStar_TypeChecker_Env.push_binders
                      goal.FStar_Tactics_Types.context [b]
                     in
                  let typ' = comp_to_typ c  in
                  let uu____2441 = new_uvar "intro" env' typ'  in
                  bind uu____2441
                    (fun u  ->
                       let uu____2447 =
                         let uu____2450 =
                           FStar_Syntax_Util.abs [b] u
                             FStar_Pervasives_Native.None
                            in
                         trysolve goal uu____2450  in
                       bind uu____2447
                         (fun bb  ->
                            if bb
                            then
                              let uu____2456 =
                                let uu____2459 =
                                  let uu___89_2460 = goal  in
                                  let uu____2461 = bnorm env' u  in
                                  let uu____2462 = bnorm env' typ'  in
                                  {
                                    FStar_Tactics_Types.context = env';
                                    FStar_Tactics_Types.witness = uu____2461;
                                    FStar_Tactics_Types.goal_ty = uu____2462;
                                    FStar_Tactics_Types.opts =
                                      (uu___89_2460.FStar_Tactics_Types.opts);
                                    FStar_Tactics_Types.is_guard =
                                      (uu___89_2460.FStar_Tactics_Types.is_guard)
                                  }  in
                                replace_cur uu____2459  in
                              bind uu____2456 (fun uu____2464  -> ret b)
                            else fail "unification failed")))
           | FStar_Pervasives_Native.None  ->
               let uu____2470 =
                 tts goal.FStar_Tactics_Types.context
                   goal.FStar_Tactics_Types.goal_ty
                  in
               fail1 "goal is not an arrow (%s)" uu____2470)
       in
    FStar_All.pipe_left (wrap_err "intro") uu____2407
  
let (intro_rec :
  Prims.unit ->
    (FStar_Syntax_Syntax.binder,FStar_Syntax_Syntax.binder)
      FStar_Pervasives_Native.tuple2 tac)
  =
  fun uu____2483  ->
    let uu____2490 = cur_goal ()  in
    bind uu____2490
      (fun goal  ->
         FStar_Util.print_string
           "WARNING (intro_rec): calling this is known to cause normalizer loops\n";
         FStar_Util.print_string
           "WARNING (intro_rec): proceed at your own risk...\n";
         (let uu____2507 =
            FStar_Syntax_Util.arrow_one goal.FStar_Tactics_Types.goal_ty  in
          match uu____2507 with
          | FStar_Pervasives_Native.Some (b,c) ->
              let uu____2526 =
                let uu____2527 = FStar_Syntax_Util.is_total_comp c  in
                Prims.op_Negation uu____2527  in
              if uu____2526
              then fail "Codomain is effectful"
              else
                (let bv =
                   FStar_Syntax_Syntax.gen_bv "__recf"
                     FStar_Pervasives_Native.None
                     goal.FStar_Tactics_Types.goal_ty
                    in
                 let bs =
                   let uu____2543 = FStar_Syntax_Syntax.mk_binder bv  in
                   [uu____2543; b]  in
                 let env' =
                   FStar_TypeChecker_Env.push_binders
                     goal.FStar_Tactics_Types.context bs
                    in
                 let uu____2545 =
                   let uu____2548 = comp_to_typ c  in
                   new_uvar "intro_rec" env' uu____2548  in
                 bind uu____2545
                   (fun u  ->
                      let lb =
                        let uu____2563 =
                          FStar_Syntax_Util.abs [b] u
                            FStar_Pervasives_Native.None
                           in
                        FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl bv)
                          [] goal.FStar_Tactics_Types.goal_ty
                          FStar_Parser_Const.effect_Tot_lid uu____2563 []
                          FStar_Range.dummyRange
                         in
                      let body = FStar_Syntax_Syntax.bv_to_name bv  in
                      let uu____2569 =
                        FStar_Syntax_Subst.close_let_rec [lb] body  in
                      match uu____2569 with
                      | (lbs,body1) ->
                          let tm =
                            FStar_Syntax_Syntax.mk
                              (FStar_Syntax_Syntax.Tm_let
                                 ((true, lbs), body1))
                              FStar_Pervasives_Native.None
                              (goal.FStar_Tactics_Types.witness).FStar_Syntax_Syntax.pos
                             in
                          let uu____2599 = trysolve goal tm  in
                          bind uu____2599
                            (fun bb  ->
                               if bb
                               then
                                 let uu____2615 =
                                   let uu____2618 =
                                     let uu___90_2619 = goal  in
                                     let uu____2620 = bnorm env' u  in
                                     let uu____2621 =
                                       let uu____2622 = comp_to_typ c  in
                                       bnorm env' uu____2622  in
                                     {
                                       FStar_Tactics_Types.context = env';
                                       FStar_Tactics_Types.witness =
                                         uu____2620;
                                       FStar_Tactics_Types.goal_ty =
                                         uu____2621;
                                       FStar_Tactics_Types.opts =
                                         (uu___90_2619.FStar_Tactics_Types.opts);
                                       FStar_Tactics_Types.is_guard =
                                         (uu___90_2619.FStar_Tactics_Types.is_guard)
                                     }  in
                                   replace_cur uu____2618  in
                                 bind uu____2615
                                   (fun uu____2629  ->
                                      let uu____2630 =
                                        let uu____2635 =
                                          FStar_Syntax_Syntax.mk_binder bv
                                           in
                                        (uu____2635, b)  in
                                      ret uu____2630)
                               else fail "intro_rec: unification failed")))
          | FStar_Pervasives_Native.None  ->
              let uu____2649 =
                tts goal.FStar_Tactics_Types.context
                  goal.FStar_Tactics_Types.goal_ty
                 in
              fail1 "intro_rec: goal is not an arrow (%s)" uu____2649))
  
let (norm : FStar_Syntax_Embeddings.norm_step Prims.list -> Prims.unit tac) =
  fun s  ->
    let uu____2665 = cur_goal ()  in
    bind uu____2665
      (fun goal  ->
         mlog
           (fun uu____2672  ->
              let uu____2673 =
                FStar_Syntax_Print.term_to_string
                  goal.FStar_Tactics_Types.witness
                 in
              FStar_Util.print1 "norm: witness = %s\n" uu____2673)
           (fun uu____2678  ->
              let steps =
                let uu____2682 = FStar_TypeChecker_Normalize.tr_norm_steps s
                   in
                FStar_List.append
                  [FStar_TypeChecker_Normalize.Reify;
                  FStar_TypeChecker_Normalize.UnfoldTac] uu____2682
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
                (let uu___91_2689 = goal  in
                 {
                   FStar_Tactics_Types.context =
                     (uu___91_2689.FStar_Tactics_Types.context);
                   FStar_Tactics_Types.witness = w;
                   FStar_Tactics_Types.goal_ty = t;
                   FStar_Tactics_Types.opts =
                     (uu___91_2689.FStar_Tactics_Types.opts);
                   FStar_Tactics_Types.is_guard =
                     (uu___91_2689.FStar_Tactics_Types.is_guard)
                 })))
  
let (norm_term_env :
  env ->
    FStar_Syntax_Embeddings.norm_step Prims.list ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac)
  =
  fun e  ->
    fun s  ->
      fun t  ->
        let uu____2707 =
          mlog
            (fun uu____2712  ->
               let uu____2713 = FStar_Syntax_Print.term_to_string t  in
               FStar_Util.print1 "norm_term: tm = %s\n" uu____2713)
            (fun uu____2715  ->
               bind get
                 (fun ps  ->
                    let opts =
                      match ps.FStar_Tactics_Types.goals with
                      | g::uu____2721 -> g.FStar_Tactics_Types.opts
                      | uu____2724 -> FStar_Options.peek ()  in
                    mlog
                      (fun uu____2729  ->
                         let uu____2730 =
                           tts ps.FStar_Tactics_Types.main_context t  in
                         FStar_Util.print1 "norm_term_env: t = %s\n"
                           uu____2730)
                      (fun uu____2733  ->
                         let uu____2734 = __tc e t  in
                         bind uu____2734
                           (fun uu____2755  ->
                              match uu____2755 with
                              | (t1,uu____2765,uu____2766) ->
                                  let steps =
                                    let uu____2770 =
                                      FStar_TypeChecker_Normalize.tr_norm_steps
                                        s
                                       in
                                    FStar_List.append
                                      [FStar_TypeChecker_Normalize.Reify;
                                      FStar_TypeChecker_Normalize.UnfoldTac]
                                      uu____2770
                                     in
                                  let t2 =
                                    normalize steps
                                      ps.FStar_Tactics_Types.main_context t1
                                     in
                                  ret t2))))
           in
        FStar_All.pipe_left (wrap_err "norm_term") uu____2707
  
let (refine_intro : Prims.unit -> Prims.unit tac) =
  fun uu____2782  ->
    let uu____2785 =
      let uu____2788 = cur_goal ()  in
      bind uu____2788
        (fun g  ->
           let uu____2795 =
             FStar_TypeChecker_Rel.base_and_refinement
               g.FStar_Tactics_Types.context g.FStar_Tactics_Types.goal_ty
              in
           match uu____2795 with
           | (uu____2808,FStar_Pervasives_Native.None ) ->
               fail "not a refinement"
           | (t,FStar_Pervasives_Native.Some (bv,phi)) ->
               let g1 =
                 let uu___92_2833 = g  in
                 {
                   FStar_Tactics_Types.context =
                     (uu___92_2833.FStar_Tactics_Types.context);
                   FStar_Tactics_Types.witness =
                     (uu___92_2833.FStar_Tactics_Types.witness);
                   FStar_Tactics_Types.goal_ty = t;
                   FStar_Tactics_Types.opts =
                     (uu___92_2833.FStar_Tactics_Types.opts);
                   FStar_Tactics_Types.is_guard =
                     (uu___92_2833.FStar_Tactics_Types.is_guard)
                 }  in
               let uu____2834 =
                 let uu____2839 =
                   let uu____2844 =
                     let uu____2845 = FStar_Syntax_Syntax.mk_binder bv  in
                     [uu____2845]  in
                   FStar_Syntax_Subst.open_term uu____2844 phi  in
                 match uu____2839 with
                 | (bvs,phi1) ->
                     let uu____2852 =
                       let uu____2853 = FStar_List.hd bvs  in
                       FStar_Pervasives_Native.fst uu____2853  in
                     (uu____2852, phi1)
                  in
               (match uu____2834 with
                | (bv1,phi1) ->
                    let uu____2866 =
                      let uu____2869 =
                        FStar_Syntax_Subst.subst
                          [FStar_Syntax_Syntax.NT
                             (bv1, (g.FStar_Tactics_Types.witness))] phi1
                         in
                      mk_irrelevant_goal "refine_intro refinement"
                        g.FStar_Tactics_Types.context uu____2869
                        g.FStar_Tactics_Types.opts
                       in
                    bind uu____2866
                      (fun g2  ->
                         bind __dismiss
                           (fun uu____2873  -> add_goals [g1; g2]))))
       in
    FStar_All.pipe_left (wrap_err "refine_intro") uu____2785
  
let (__exact_now : Prims.bool -> FStar_Syntax_Syntax.term -> Prims.unit tac)
  =
  fun set_expected_typ1  ->
    fun t  ->
      let uu____2888 = cur_goal ()  in
      bind uu____2888
        (fun goal  ->
           let env =
             if set_expected_typ1
             then
               FStar_TypeChecker_Env.set_expected_typ
                 goal.FStar_Tactics_Types.context
                 goal.FStar_Tactics_Types.goal_ty
             else goal.FStar_Tactics_Types.context  in
           let uu____2897 = __tc env t  in
           bind uu____2897
             (fun uu____2916  ->
                match uu____2916 with
                | (t1,typ,guard) ->
                    mlog
                      (fun uu____2931  ->
                         let uu____2932 =
                           tts goal.FStar_Tactics_Types.context typ  in
                         let uu____2933 =
                           FStar_TypeChecker_Rel.guard_to_string
                             goal.FStar_Tactics_Types.context guard
                            in
                         FStar_Util.print2
                           "__exact_now: got type %s\n__exact_now and guard %s\n"
                           uu____2932 uu____2933)
                      (fun uu____2936  ->
                         let uu____2937 =
                           proc_guard "__exact typing"
                             goal.FStar_Tactics_Types.context guard
                             goal.FStar_Tactics_Types.opts
                            in
                         bind uu____2937
                           (fun uu____2941  ->
                              mlog
                                (fun uu____2945  ->
                                   let uu____2946 =
                                     tts goal.FStar_Tactics_Types.context typ
                                      in
                                   let uu____2947 =
                                     tts goal.FStar_Tactics_Types.context
                                       goal.FStar_Tactics_Types.goal_ty
                                      in
                                   FStar_Util.print2
                                     "__exact_now: unifying %s and %s\n"
                                     uu____2946 uu____2947)
                                (fun uu____2950  ->
                                   let uu____2951 =
                                     do_unify
                                       goal.FStar_Tactics_Types.context typ
                                       goal.FStar_Tactics_Types.goal_ty
                                      in
                                   bind uu____2951
                                     (fun b  ->
                                        if b
                                        then solve goal t1
                                        else
                                          (let uu____2959 =
                                             tts
                                               goal.FStar_Tactics_Types.context
                                               t1
                                              in
                                           let uu____2960 =
                                             tts
                                               goal.FStar_Tactics_Types.context
                                               typ
                                              in
                                           let uu____2961 =
                                             tts
                                               goal.FStar_Tactics_Types.context
                                               goal.FStar_Tactics_Types.goal_ty
                                              in
                                           let uu____2962 =
                                             tts
                                               goal.FStar_Tactics_Types.context
                                               goal.FStar_Tactics_Types.witness
                                              in
                                           fail4
                                             "%s : %s does not exactly solve the goal %s (witness = %s)"
                                             uu____2959 uu____2960 uu____2961
                                             uu____2962)))))))
  
let (t_exact : Prims.bool -> FStar_Syntax_Syntax.term -> Prims.unit tac) =
  fun set_expected_typ1  ->
    fun tm  ->
      let uu____2973 =
        mlog
          (fun uu____2978  ->
             let uu____2979 = FStar_Syntax_Print.term_to_string tm  in
             FStar_Util.print1 "t_exact: tm = %s\n" uu____2979)
          (fun uu____2982  ->
             let uu____2983 =
               let uu____2990 = __exact_now set_expected_typ1 tm  in
               trytac' uu____2990  in
             bind uu____2983
               (fun uu___58_2999  ->
                  match uu___58_2999 with
                  | FStar_Util.Inr r -> ret ()
                  | FStar_Util.Inl e ->
                      let uu____3008 =
                        let uu____3015 =
                          let uu____3018 =
                            norm [FStar_Syntax_Embeddings.Delta]  in
                          bind uu____3018
                            (fun uu____3023  ->
                               let uu____3024 = refine_intro ()  in
                               bind uu____3024
                                 (fun uu____3028  ->
                                    __exact_now set_expected_typ1 tm))
                           in
                        trytac' uu____3015  in
                      bind uu____3008
                        (fun uu___57_3035  ->
                           match uu___57_3035 with
                           | FStar_Util.Inr r -> ret ()
                           | FStar_Util.Inl uu____3043 -> fail e)))
         in
      FStar_All.pipe_left (wrap_err "exact") uu____2973
  
let (uvar_free_in_goal :
  FStar_Syntax_Syntax.uvar -> FStar_Tactics_Types.goal -> Prims.bool) =
  fun u  ->
    fun g  ->
      if g.FStar_Tactics_Types.is_guard
      then false
      else
        (let free_uvars =
           let uu____3058 =
             let uu____3065 =
               FStar_Syntax_Free.uvars g.FStar_Tactics_Types.goal_ty  in
             FStar_Util.set_elements uu____3065  in
           FStar_List.map FStar_Pervasives_Native.fst uu____3058  in
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
          let uu____3125 = f x  in
          bind uu____3125
            (fun y  ->
               let uu____3133 = mapM f xs  in
               bind uu____3133 (fun ys  -> ret (y :: ys)))
  
exception NoUnif 
let (uu___is_NoUnif : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with | NoUnif  -> true | uu____3151 -> false
  
let rec (__apply :
  Prims.bool ->
    FStar_Syntax_Syntax.term -> FStar_Reflection_Data.typ -> Prims.unit tac)
  =
  fun uopt  ->
    fun tm  ->
      fun typ  ->
        let uu____3165 = cur_goal ()  in
        bind uu____3165
          (fun goal  ->
             mlog
               (fun uu____3172  ->
                  let uu____3173 = FStar_Syntax_Print.term_to_string tm  in
                  FStar_Util.print1 ">>> Calling __exact(%s)\n" uu____3173)
               (fun uu____3176  ->
                  let uu____3177 =
                    let uu____3182 =
                      let uu____3185 = t_exact false tm  in
                      with_policy FStar_Tactics_Types.Force uu____3185  in
                    trytac_exn uu____3182  in
                  bind uu____3177
                    (fun uu___59_3192  ->
                       match uu___59_3192 with
                       | FStar_Pervasives_Native.Some r -> ret ()
                       | FStar_Pervasives_Native.None  ->
                           mlog
                             (fun uu____3200  ->
                                let uu____3201 =
                                  FStar_Syntax_Print.term_to_string typ  in
                                FStar_Util.print1 ">>> typ = %s\n" uu____3201)
                             (fun uu____3204  ->
                                let uu____3205 =
                                  FStar_Syntax_Util.arrow_one typ  in
                                match uu____3205 with
                                | FStar_Pervasives_Native.None  ->
                                    FStar_Exn.raise NoUnif
                                | FStar_Pervasives_Native.Some ((bv,aq),c) ->
                                    mlog
                                      (fun uu____3237  ->
                                         let uu____3238 =
                                           FStar_Syntax_Print.binder_to_string
                                             (bv, aq)
                                            in
                                         FStar_Util.print1
                                           "__apply: pushing binder %s\n"
                                           uu____3238)
                                      (fun uu____3241  ->
                                         let uu____3242 =
                                           let uu____3243 =
                                             FStar_Syntax_Util.is_total_comp
                                               c
                                              in
                                           Prims.op_Negation uu____3243  in
                                         if uu____3242
                                         then
                                           fail "apply: not total codomain"
                                         else
                                           (let uu____3247 =
                                              new_uvar "apply"
                                                goal.FStar_Tactics_Types.context
                                                bv.FStar_Syntax_Syntax.sort
                                               in
                                            bind uu____3247
                                              (fun u  ->
                                                 let tm' =
                                                   FStar_Syntax_Syntax.mk_Tm_app
                                                     tm [(u, aq)]
                                                     FStar_Pervasives_Native.None
                                                     tm.FStar_Syntax_Syntax.pos
                                                    in
                                                 let typ' =
                                                   let uu____3267 =
                                                     comp_to_typ c  in
                                                   FStar_All.pipe_left
                                                     (FStar_Syntax_Subst.subst
                                                        [FStar_Syntax_Syntax.NT
                                                           (bv, u)])
                                                     uu____3267
                                                    in
                                                 let uu____3268 =
                                                   __apply uopt tm' typ'  in
                                                 bind uu____3268
                                                   (fun uu____3276  ->
                                                      let u1 =
                                                        bnorm
                                                          goal.FStar_Tactics_Types.context
                                                          u
                                                         in
                                                      let uu____3278 =
                                                        let uu____3279 =
                                                          let uu____3282 =
                                                            let uu____3283 =
                                                              FStar_Syntax_Util.head_and_args
                                                                u1
                                                               in
                                                            FStar_Pervasives_Native.fst
                                                              uu____3283
                                                             in
                                                          FStar_Syntax_Subst.compress
                                                            uu____3282
                                                           in
                                                        uu____3279.FStar_Syntax_Syntax.n
                                                         in
                                                      match uu____3278 with
                                                      | FStar_Syntax_Syntax.Tm_uvar
                                                          (uvar,uu____3311)
                                                          ->
                                                          bind get
                                                            (fun ps  ->
                                                               let uu____3339
                                                                 =
                                                                 uopt &&
                                                                   (uvar_free
                                                                    uvar ps)
                                                                  in
                                                               if uu____3339
                                                               then ret ()
                                                               else
                                                                 (let uu____3343
                                                                    =
                                                                    let uu____3346
                                                                    =
                                                                    let uu___93_3347
                                                                    = goal
                                                                     in
                                                                    let uu____3348
                                                                    =
                                                                    bnorm
                                                                    goal.FStar_Tactics_Types.context
                                                                    u1  in
                                                                    let uu____3349
                                                                    =
                                                                    bnorm
                                                                    goal.FStar_Tactics_Types.context
                                                                    bv.FStar_Syntax_Syntax.sort
                                                                     in
                                                                    {
                                                                    FStar_Tactics_Types.context
                                                                    =
                                                                    (uu___93_3347.FStar_Tactics_Types.context);
                                                                    FStar_Tactics_Types.witness
                                                                    =
                                                                    uu____3348;
                                                                    FStar_Tactics_Types.goal_ty
                                                                    =
                                                                    uu____3349;
                                                                    FStar_Tactics_Types.opts
                                                                    =
                                                                    (uu___93_3347.FStar_Tactics_Types.opts);
                                                                    FStar_Tactics_Types.is_guard
                                                                    = false
                                                                    }  in
                                                                    [uu____3346]
                                                                     in
                                                                  add_goals
                                                                    uu____3343))
                                                      | t -> ret ()))))))))
  
let try_unif : 'a . 'a tac -> 'a tac -> 'a tac =
  fun t  ->
    fun t'  -> mk_tac (fun ps  -> try run t ps with | NoUnif  -> run t' ps)
  
let (apply : Prims.bool -> FStar_Syntax_Syntax.term -> Prims.unit tac) =
  fun uopt  ->
    fun tm  ->
      let uu____3395 =
        mlog
          (fun uu____3400  ->
             let uu____3401 = FStar_Syntax_Print.term_to_string tm  in
             FStar_Util.print1 "apply: tm = %s\n" uu____3401)
          (fun uu____3404  ->
             let uu____3405 = cur_goal ()  in
             bind uu____3405
               (fun goal  ->
                  let uu____3411 = __tc goal.FStar_Tactics_Types.context tm
                     in
                  bind uu____3411
                    (fun uu____3433  ->
                       match uu____3433 with
                       | (tm1,typ,guard) ->
                           let typ1 =
                             bnorm goal.FStar_Tactics_Types.context typ  in
                           let uu____3446 =
                             let uu____3449 =
                               let uu____3452 = __apply uopt tm1 typ1  in
                               bind uu____3452
                                 (fun uu____3456  ->
                                    proc_guard "apply guard"
                                      goal.FStar_Tactics_Types.context guard
                                      goal.FStar_Tactics_Types.opts)
                                in
                             focus uu____3449  in
                           let uu____3457 =
                             let uu____3460 =
                               tts goal.FStar_Tactics_Types.context tm1  in
                             let uu____3461 =
                               tts goal.FStar_Tactics_Types.context typ1  in
                             let uu____3462 =
                               tts goal.FStar_Tactics_Types.context
                                 goal.FStar_Tactics_Types.goal_ty
                                in
                             fail3
                               "Cannot instantiate %s (of type %s) to match goal (%s)"
                               uu____3460 uu____3461 uu____3462
                              in
                           try_unif uu____3446 uu____3457)))
         in
      FStar_All.pipe_left (wrap_err "apply") uu____3395
  
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
      let uu____3489 =
        match ct.FStar_Syntax_Syntax.effect_args with
        | pre::post::uu____3508 ->
            ((FStar_Pervasives_Native.fst pre),
              (FStar_Pervasives_Native.fst post))
        | uu____3549 -> failwith "apply_lemma: impossible: not a lemma"  in
      match uu____3489 with
      | (pre,post) ->
          let post1 =
            let uu____3585 =
              let uu____3594 =
                FStar_Syntax_Syntax.as_arg FStar_Syntax_Util.exp_unit  in
              [uu____3594]  in
            FStar_Syntax_Util.mk_app post uu____3585  in
          FStar_Pervasives_Native.Some (pre, post1)
    else
      if FStar_Syntax_Util.is_pure_effect ct.FStar_Syntax_Syntax.effect_name
      then
        (let uu____3614 =
           FStar_Syntax_Util.un_squash ct.FStar_Syntax_Syntax.result_typ  in
         FStar_Util.map_opt uu____3614
           (fun post  -> (FStar_Syntax_Util.t_true, post)))
      else FStar_Pervasives_Native.None
  
let (apply_lemma : FStar_Syntax_Syntax.term -> Prims.unit tac) =
  fun tm  ->
    let uu____3645 =
      let uu____3648 =
        mlog
          (fun uu____3653  ->
             let uu____3654 = FStar_Syntax_Print.term_to_string tm  in
             FStar_Util.print1 "apply_lemma: tm = %s\n" uu____3654)
          (fun uu____3658  ->
             let is_unit_t t =
               let uu____3663 =
                 let uu____3664 = FStar_Syntax_Subst.compress t  in
                 uu____3664.FStar_Syntax_Syntax.n  in
               match uu____3663 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.unit_lid
                   -> true
               | uu____3668 -> false  in
             let uu____3669 = cur_goal ()  in
             bind uu____3669
               (fun goal  ->
                  let uu____3675 = __tc goal.FStar_Tactics_Types.context tm
                     in
                  bind uu____3675
                    (fun uu____3698  ->
                       match uu____3698 with
                       | (tm1,t,guard) ->
                           let uu____3710 =
                             FStar_Syntax_Util.arrow_formals_comp t  in
                           (match uu____3710 with
                            | (bs,comp) ->
                                let uu____3737 = lemma_or_sq comp  in
                                (match uu____3737 with
                                 | FStar_Pervasives_Native.None  ->
                                     fail "not a lemma or squashed function"
                                 | FStar_Pervasives_Native.Some (pre,post) ->
                                     let uu____3756 =
                                       FStar_List.fold_left
                                         (fun uu____3802  ->
                                            fun uu____3803  ->
                                              match (uu____3802, uu____3803)
                                              with
                                              | ((uvs,guard1,subst1),(b,aq))
                                                  ->
                                                  let b_t =
                                                    FStar_Syntax_Subst.subst
                                                      subst1
                                                      b.FStar_Syntax_Syntax.sort
                                                     in
                                                  let uu____3906 =
                                                    is_unit_t b_t  in
                                                  if uu____3906
                                                  then
                                                    (((FStar_Syntax_Util.exp_unit,
                                                        aq) :: uvs), guard1,
                                                      ((FStar_Syntax_Syntax.NT
                                                          (b,
                                                            FStar_Syntax_Util.exp_unit))
                                                      :: subst1))
                                                  else
                                                    (let uu____3944 =
                                                       FStar_TypeChecker_Util.new_implicit_var
                                                         "apply_lemma"
                                                         (goal.FStar_Tactics_Types.goal_ty).FStar_Syntax_Syntax.pos
                                                         goal.FStar_Tactics_Types.context
                                                         b_t
                                                        in
                                                     match uu____3944 with
                                                     | (u,uu____3974,g_u) ->
                                                         let uu____3988 =
                                                           FStar_TypeChecker_Rel.conj_guard
                                                             guard1 g_u
                                                            in
                                                         (((u, aq) :: uvs),
                                                           uu____3988,
                                                           ((FStar_Syntax_Syntax.NT
                                                               (b, u)) ::
                                                           subst1))))
                                         ([], guard, []) bs
                                        in
                                     (match uu____3756 with
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
                                          let uu____4059 =
                                            let uu____4062 =
                                              FStar_Syntax_Util.mk_squash
                                                FStar_Syntax_Syntax.U_zero
                                                post1
                                               in
                                            do_unify
                                              goal.FStar_Tactics_Types.context
                                              uu____4062
                                              goal.FStar_Tactics_Types.goal_ty
                                             in
                                          bind uu____4059
                                            (fun b  ->
                                               if Prims.op_Negation b
                                               then
                                                 let uu____4070 =
                                                   tts
                                                     goal.FStar_Tactics_Types.context
                                                     tm1
                                                    in
                                                 let uu____4071 =
                                                   let uu____4072 =
                                                     FStar_Syntax_Util.mk_squash
                                                       FStar_Syntax_Syntax.U_zero
                                                       post1
                                                      in
                                                   tts
                                                     goal.FStar_Tactics_Types.context
                                                     uu____4072
                                                    in
                                                 let uu____4073 =
                                                   tts
                                                     goal.FStar_Tactics_Types.context
                                                     goal.FStar_Tactics_Types.goal_ty
                                                    in
                                                 fail3
                                                   "Cannot instantiate lemma %s (with postcondition: %s) to match goal (%s)"
                                                   uu____4070 uu____4071
                                                   uu____4073
                                               else
                                                 (let uu____4075 =
                                                    add_implicits
                                                      implicits.FStar_TypeChecker_Env.implicits
                                                     in
                                                  bind uu____4075
                                                    (fun uu____4080  ->
                                                       let uu____4081 =
                                                         solve goal
                                                           FStar_Syntax_Util.exp_unit
                                                          in
                                                       bind uu____4081
                                                         (fun uu____4089  ->
                                                            let is_free_uvar
                                                              uv t1 =
                                                              let free_uvars
                                                                =
                                                                let uu____4100
                                                                  =
                                                                  let uu____4107
                                                                    =
                                                                    FStar_Syntax_Free.uvars
                                                                    t1  in
                                                                  FStar_Util.set_elements
                                                                    uu____4107
                                                                   in
                                                                FStar_List.map
                                                                  FStar_Pervasives_Native.fst
                                                                  uu____4100
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
                                                              let uu____4148
                                                                =
                                                                FStar_Syntax_Util.head_and_args
                                                                  t1
                                                                 in
                                                              match uu____4148
                                                              with
                                                              | (hd1,uu____4164)
                                                                  ->
                                                                  (match 
                                                                    hd1.FStar_Syntax_Syntax.n
                                                                   with
                                                                   | 
                                                                   FStar_Syntax_Syntax.Tm_uvar
                                                                    (uv,uu____4186)
                                                                    ->
                                                                    appears
                                                                    uv goals
                                                                   | 
                                                                   uu____4211
                                                                    -> false)
                                                               in
                                                            let uu____4212 =
                                                              FStar_All.pipe_right
                                                                implicits.FStar_TypeChecker_Env.implicits
                                                                (mapM
                                                                   (fun
                                                                    uu____4284
                                                                     ->
                                                                    match uu____4284
                                                                    with
                                                                    | 
                                                                    (_msg,env,_uvar,term,typ,uu____4312)
                                                                    ->
                                                                    let uu____4313
                                                                    =
                                                                    FStar_Syntax_Util.head_and_args
                                                                    term  in
                                                                    (match uu____4313
                                                                    with
                                                                    | 
                                                                    (hd1,uu____4339)
                                                                    ->
                                                                    let uu____4360
                                                                    =
                                                                    let uu____4361
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    hd1  in
                                                                    uu____4361.FStar_Syntax_Syntax.n
                                                                     in
                                                                    (match uu____4360
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Tm_uvar
                                                                    uu____4374
                                                                    ->
                                                                    let uu____4391
                                                                    =
                                                                    let uu____4400
                                                                    =
                                                                    let uu____4403
                                                                    =
                                                                    let uu___96_4404
                                                                    = goal
                                                                     in
                                                                    let uu____4405
                                                                    =
                                                                    bnorm
                                                                    goal.FStar_Tactics_Types.context
                                                                    term  in
                                                                    let uu____4406
                                                                    =
                                                                    bnorm
                                                                    goal.FStar_Tactics_Types.context
                                                                    typ  in
                                                                    {
                                                                    FStar_Tactics_Types.context
                                                                    =
                                                                    (uu___96_4404.FStar_Tactics_Types.context);
                                                                    FStar_Tactics_Types.witness
                                                                    =
                                                                    uu____4405;
                                                                    FStar_Tactics_Types.goal_ty
                                                                    =
                                                                    uu____4406;
                                                                    FStar_Tactics_Types.opts
                                                                    =
                                                                    (uu___96_4404.FStar_Tactics_Types.opts);
                                                                    FStar_Tactics_Types.is_guard
                                                                    =
                                                                    (uu___96_4404.FStar_Tactics_Types.is_guard)
                                                                    }  in
                                                                    [uu____4403]
                                                                     in
                                                                    (uu____4400,
                                                                    [])  in
                                                                    ret
                                                                    uu____4391
                                                                    | 
                                                                    uu____4419
                                                                    ->
                                                                    let g_typ
                                                                    =
                                                                    let uu____4421
                                                                    =
                                                                    FStar_Options.__temp_fast_implicits
                                                                    ()  in
                                                                    if
                                                                    uu____4421
                                                                    then
                                                                    FStar_TypeChecker_TcTerm.check_type_of_well_typed_term
                                                                    false env
                                                                    term typ
                                                                    else
                                                                    (let term1
                                                                    =
                                                                    bnorm env
                                                                    term  in
                                                                    let uu____4424
                                                                    =
                                                                    let uu____4431
                                                                    =
                                                                    FStar_TypeChecker_Env.set_expected_typ
                                                                    env typ
                                                                     in
                                                                    env.FStar_TypeChecker_Env.type_of
                                                                    uu____4431
                                                                    term1  in
                                                                    match uu____4424
                                                                    with
                                                                    | 
                                                                    (uu____4432,uu____4433,g_typ)
                                                                    -> g_typ)
                                                                     in
                                                                    let uu____4435
                                                                    =
                                                                    goal_from_guard
                                                                    "apply_lemma solved arg"
                                                                    goal.FStar_Tactics_Types.context
                                                                    g_typ
                                                                    goal.FStar_Tactics_Types.opts
                                                                     in
                                                                    bind
                                                                    uu____4435
                                                                    (fun
                                                                    uu___60_4451
                                                                     ->
                                                                    match uu___60_4451
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
                                                            bind uu____4212
                                                              (fun goals_  ->
                                                                 let sub_goals
                                                                   =
                                                                   let uu____4519
                                                                    =
                                                                    FStar_List.map
                                                                    FStar_Pervasives_Native.fst
                                                                    goals_
                                                                     in
                                                                   FStar_List.flatten
                                                                    uu____4519
                                                                    in
                                                                 let smt_goals
                                                                   =
                                                                   let uu____4541
                                                                    =
                                                                    FStar_List.map
                                                                    FStar_Pervasives_Native.snd
                                                                    goals_
                                                                     in
                                                                   FStar_List.flatten
                                                                    uu____4541
                                                                    in
                                                                 let rec filter'
                                                                   a f xs =
                                                                   match xs
                                                                   with
                                                                   | 
                                                                   [] -> []
                                                                   | 
                                                                   x::xs1 ->
                                                                    let uu____4596
                                                                    = f x xs1
                                                                     in
                                                                    if
                                                                    uu____4596
                                                                    then
                                                                    let uu____4599
                                                                    =
                                                                    filter'
                                                                    () f xs1
                                                                     in x ::
                                                                    uu____4599
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
                                                                    let uu____4613
                                                                    =
                                                                    checkone
                                                                    g.FStar_Tactics_Types.witness
                                                                    goals  in
                                                                    Prims.op_Negation
                                                                    uu____4613))
                                                                    a438 a439)
                                                                    (Obj.magic
                                                                    sub_goals))
                                                                    in
                                                                 let uu____4614
                                                                   =
                                                                   proc_guard
                                                                    "apply_lemma guard"
                                                                    goal.FStar_Tactics_Types.context
                                                                    guard
                                                                    goal.FStar_Tactics_Types.opts
                                                                    in
                                                                 bind
                                                                   uu____4614
                                                                   (fun
                                                                    uu____4619
                                                                     ->
                                                                    let uu____4620
                                                                    =
                                                                    let uu____4623
                                                                    =
                                                                    let uu____4624
                                                                    =
                                                                    let uu____4625
                                                                    =
                                                                    FStar_Syntax_Util.mk_squash
                                                                    FStar_Syntax_Syntax.U_zero
                                                                    pre1  in
                                                                    istrivial
                                                                    goal.FStar_Tactics_Types.context
                                                                    uu____4625
                                                                     in
                                                                    Prims.op_Negation
                                                                    uu____4624
                                                                     in
                                                                    if
                                                                    uu____4623
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
                                                                    uu____4620
                                                                    (fun
                                                                    uu____4631
                                                                     ->
                                                                    let uu____4632
                                                                    =
                                                                    add_smt_goals
                                                                    smt_goals
                                                                     in
                                                                    bind
                                                                    uu____4632
                                                                    (fun
                                                                    uu____4636
                                                                     ->
                                                                    add_goals
                                                                    sub_goals1))))))))))))))
         in
      focus uu____3648  in
    FStar_All.pipe_left (wrap_err "apply_lemma") uu____3645
  
let (destruct_eq' :
  FStar_Reflection_Data.typ ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun typ  ->
    let uu____4656 = FStar_Syntax_Util.destruct_typ_as_formula typ  in
    match uu____4656 with
    | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn
        (l,uu____4666::(e1,uu____4668)::(e2,uu____4670)::[])) when
        FStar_Ident.lid_equals l FStar_Parser_Const.eq2_lid ->
        FStar_Pervasives_Native.Some (e1, e2)
    | uu____4729 -> FStar_Pervasives_Native.None
  
let (destruct_eq :
  FStar_Reflection_Data.typ ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun typ  ->
    let uu____4751 = destruct_eq' typ  in
    match uu____4751 with
    | FStar_Pervasives_Native.Some t -> FStar_Pervasives_Native.Some t
    | FStar_Pervasives_Native.None  ->
        let uu____4781 = FStar_Syntax_Util.un_squash typ  in
        (match uu____4781 with
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
        let uu____4837 = FStar_TypeChecker_Env.pop_bv e1  in
        match uu____4837 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (bv',e') ->
            if FStar_Syntax_Syntax.bv_eq bvar bv'
            then FStar_Pervasives_Native.Some (e', [])
            else
              (let uu____4885 = aux e'  in
               FStar_Util.map_opt uu____4885
                 (fun uu____4909  ->
                    match uu____4909 with | (e'',bvs) -> (e'', (bv' :: bvs))))
         in
      let uu____4930 = aux e  in
      FStar_Util.map_opt uu____4930
        (fun uu____4954  ->
           match uu____4954 with | (e',bvs) -> (e', (FStar_List.rev bvs)))
  
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
          let uu____5009 = split_env b1 g.FStar_Tactics_Types.context  in
          FStar_Util.map_opt uu____5009
            (fun uu____5033  ->
               match uu____5033 with
               | (e0,bvs) ->
                   let s1 bv =
                     let uu___97_5050 = bv  in
                     let uu____5051 =
                       FStar_Syntax_Subst.subst s bv.FStar_Syntax_Syntax.sort
                        in
                     {
                       FStar_Syntax_Syntax.ppname =
                         (uu___97_5050.FStar_Syntax_Syntax.ppname);
                       FStar_Syntax_Syntax.index =
                         (uu___97_5050.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort = uu____5051
                     }  in
                   let bvs1 = FStar_List.map s1 bvs  in
                   let c = push_bvs e0 (b2 :: bvs1)  in
                   let w =
                     FStar_Syntax_Subst.subst s g.FStar_Tactics_Types.witness
                      in
                   let t =
                     FStar_Syntax_Subst.subst s g.FStar_Tactics_Types.goal_ty
                      in
                   let uu___98_5060 = g  in
                   {
                     FStar_Tactics_Types.context = c;
                     FStar_Tactics_Types.witness = w;
                     FStar_Tactics_Types.goal_ty = t;
                     FStar_Tactics_Types.opts =
                       (uu___98_5060.FStar_Tactics_Types.opts);
                     FStar_Tactics_Types.is_guard =
                       (uu___98_5060.FStar_Tactics_Types.is_guard)
                   })
  
let (rewrite : FStar_Syntax_Syntax.binder -> Prims.unit tac) =
  fun h  ->
    let uu____5068 = cur_goal ()  in
    bind uu____5068
      (fun goal  ->
         let uu____5076 = h  in
         match uu____5076 with
         | (bv,uu____5080) ->
             mlog
               (fun uu____5084  ->
                  let uu____5085 = FStar_Syntax_Print.bv_to_string bv  in
                  let uu____5086 =
                    tts goal.FStar_Tactics_Types.context
                      bv.FStar_Syntax_Syntax.sort
                     in
                  FStar_Util.print2 "+++Rewrite %s : %s\n" uu____5085
                    uu____5086)
               (fun uu____5089  ->
                  let uu____5090 =
                    split_env bv goal.FStar_Tactics_Types.context  in
                  match uu____5090 with
                  | FStar_Pervasives_Native.None  ->
                      fail "rewrite: binder not found in environment"
                  | FStar_Pervasives_Native.Some (e0,bvs) ->
                      let uu____5119 =
                        destruct_eq bv.FStar_Syntax_Syntax.sort  in
                      (match uu____5119 with
                       | FStar_Pervasives_Native.Some (x,e) ->
                           let uu____5134 =
                             let uu____5135 = FStar_Syntax_Subst.compress x
                                in
                             uu____5135.FStar_Syntax_Syntax.n  in
                           (match uu____5134 with
                            | FStar_Syntax_Syntax.Tm_name x1 ->
                                let s = [FStar_Syntax_Syntax.NT (x1, e)]  in
                                let s1 bv1 =
                                  let uu___99_5148 = bv1  in
                                  let uu____5149 =
                                    FStar_Syntax_Subst.subst s
                                      bv1.FStar_Syntax_Syntax.sort
                                     in
                                  {
                                    FStar_Syntax_Syntax.ppname =
                                      (uu___99_5148.FStar_Syntax_Syntax.ppname);
                                    FStar_Syntax_Syntax.index =
                                      (uu___99_5148.FStar_Syntax_Syntax.index);
                                    FStar_Syntax_Syntax.sort = uu____5149
                                  }  in
                                let bvs1 = FStar_List.map s1 bvs  in
                                let uu____5155 =
                                  let uu___100_5156 = goal  in
                                  let uu____5157 = push_bvs e0 (bv :: bvs1)
                                     in
                                  let uu____5158 =
                                    FStar_Syntax_Subst.subst s
                                      goal.FStar_Tactics_Types.witness
                                     in
                                  let uu____5159 =
                                    FStar_Syntax_Subst.subst s
                                      goal.FStar_Tactics_Types.goal_ty
                                     in
                                  {
                                    FStar_Tactics_Types.context = uu____5157;
                                    FStar_Tactics_Types.witness = uu____5158;
                                    FStar_Tactics_Types.goal_ty = uu____5159;
                                    FStar_Tactics_Types.opts =
                                      (uu___100_5156.FStar_Tactics_Types.opts);
                                    FStar_Tactics_Types.is_guard =
                                      (uu___100_5156.FStar_Tactics_Types.is_guard)
                                  }  in
                                replace_cur uu____5155
                            | uu____5160 ->
                                fail
                                  "rewrite: Not an equality hypothesis with a variable on the LHS")
                       | uu____5161 ->
                           fail "rewrite: Not an equality hypothesis")))
  
let (rename_to :
  FStar_Syntax_Syntax.binder -> Prims.string -> Prims.unit tac) =
  fun b  ->
    fun s  ->
      let uu____5178 = cur_goal ()  in
      bind uu____5178
        (fun goal  ->
           let uu____5189 = b  in
           match uu____5189 with
           | (bv,uu____5193) ->
               let bv' =
                 FStar_Syntax_Syntax.freshen_bv
                   (let uu___101_5197 = bv  in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (FStar_Ident.mk_ident
                           (s,
                             ((bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange)));
                      FStar_Syntax_Syntax.index =
                        (uu___101_5197.FStar_Syntax_Syntax.index);
                      FStar_Syntax_Syntax.sort =
                        (uu___101_5197.FStar_Syntax_Syntax.sort)
                    })
                  in
               let s1 =
                 let uu____5201 =
                   let uu____5202 =
                     let uu____5209 = FStar_Syntax_Syntax.bv_to_name bv'  in
                     (bv, uu____5209)  in
                   FStar_Syntax_Syntax.NT uu____5202  in
                 [uu____5201]  in
               let uu____5210 = subst_goal bv bv' s1 goal  in
               (match uu____5210 with
                | FStar_Pervasives_Native.None  ->
                    fail "rename_to: binder not found in environment"
                | FStar_Pervasives_Native.Some goal1 -> replace_cur goal1))
  
let (binder_retype : FStar_Syntax_Syntax.binder -> Prims.unit tac) =
  fun b  ->
    let uu____5223 = cur_goal ()  in
    bind uu____5223
      (fun goal  ->
         let uu____5232 = b  in
         match uu____5232 with
         | (bv,uu____5236) ->
             let uu____5237 = split_env bv goal.FStar_Tactics_Types.context
                in
             (match uu____5237 with
              | FStar_Pervasives_Native.None  ->
                  fail "binder_retype: binder is not present in environment"
              | FStar_Pervasives_Native.Some (e0,bvs) ->
                  let uu____5266 = FStar_Syntax_Util.type_u ()  in
                  (match uu____5266 with
                   | (ty,u) ->
                       let uu____5275 = new_uvar "binder_retype" e0 ty  in
                       bind uu____5275
                         (fun t'  ->
                            let bv'' =
                              let uu___102_5285 = bv  in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___102_5285.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___102_5285.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = t'
                              }  in
                            let s =
                              let uu____5289 =
                                let uu____5290 =
                                  let uu____5297 =
                                    FStar_Syntax_Syntax.bv_to_name bv''  in
                                  (bv, uu____5297)  in
                                FStar_Syntax_Syntax.NT uu____5290  in
                              [uu____5289]  in
                            let bvs1 =
                              FStar_List.map
                                (fun b1  ->
                                   let uu___103_5305 = b1  in
                                   let uu____5306 =
                                     FStar_Syntax_Subst.subst s
                                       b1.FStar_Syntax_Syntax.sort
                                      in
                                   {
                                     FStar_Syntax_Syntax.ppname =
                                       (uu___103_5305.FStar_Syntax_Syntax.ppname);
                                     FStar_Syntax_Syntax.index =
                                       (uu___103_5305.FStar_Syntax_Syntax.index);
                                     FStar_Syntax_Syntax.sort = uu____5306
                                   }) bvs
                               in
                            let env' = push_bvs e0 (bv'' :: bvs1)  in
                            bind __dismiss
                              (fun uu____5312  ->
                                 let uu____5313 =
                                   let uu____5316 =
                                     let uu____5319 =
                                       let uu___104_5320 = goal  in
                                       let uu____5321 =
                                         FStar_Syntax_Subst.subst s
                                           goal.FStar_Tactics_Types.witness
                                          in
                                       let uu____5322 =
                                         FStar_Syntax_Subst.subst s
                                           goal.FStar_Tactics_Types.goal_ty
                                          in
                                       {
                                         FStar_Tactics_Types.context = env';
                                         FStar_Tactics_Types.witness =
                                           uu____5321;
                                         FStar_Tactics_Types.goal_ty =
                                           uu____5322;
                                         FStar_Tactics_Types.opts =
                                           (uu___104_5320.FStar_Tactics_Types.opts);
                                         FStar_Tactics_Types.is_guard =
                                           (uu___104_5320.FStar_Tactics_Types.is_guard)
                                       }  in
                                     [uu____5319]  in
                                   add_goals uu____5316  in
                                 bind uu____5313
                                   (fun uu____5325  ->
                                      let uu____5326 =
                                        FStar_Syntax_Util.mk_eq2
                                          (FStar_Syntax_Syntax.U_succ u) ty
                                          bv.FStar_Syntax_Syntax.sort t'
                                         in
                                      add_irrelevant_goal
                                        "binder_retype equation" e0
                                        uu____5326
                                        goal.FStar_Tactics_Types.opts))))))
  
let (norm_binder_type :
  FStar_Syntax_Embeddings.norm_step Prims.list ->
    FStar_Syntax_Syntax.binder -> Prims.unit tac)
  =
  fun s  ->
    fun b  ->
      let uu____5341 = cur_goal ()  in
      bind uu____5341
        (fun goal  ->
           let uu____5350 = b  in
           match uu____5350 with
           | (bv,uu____5354) ->
               let uu____5355 = split_env bv goal.FStar_Tactics_Types.context
                  in
               (match uu____5355 with
                | FStar_Pervasives_Native.None  ->
                    fail
                      "binder_retype: binder is not present in environment"
                | FStar_Pervasives_Native.Some (e0,bvs) ->
                    let steps =
                      let uu____5387 =
                        FStar_TypeChecker_Normalize.tr_norm_steps s  in
                      FStar_List.append
                        [FStar_TypeChecker_Normalize.Reify;
                        FStar_TypeChecker_Normalize.UnfoldTac] uu____5387
                       in
                    let sort' =
                      normalize steps e0 bv.FStar_Syntax_Syntax.sort  in
                    let bv' =
                      let uu___105_5392 = bv  in
                      {
                        FStar_Syntax_Syntax.ppname =
                          (uu___105_5392.FStar_Syntax_Syntax.ppname);
                        FStar_Syntax_Syntax.index =
                          (uu___105_5392.FStar_Syntax_Syntax.index);
                        FStar_Syntax_Syntax.sort = sort'
                      }  in
                    let env' = push_bvs e0 (bv' :: bvs)  in
                    replace_cur
                      (let uu___106_5396 = goal  in
                       {
                         FStar_Tactics_Types.context = env';
                         FStar_Tactics_Types.witness =
                           (uu___106_5396.FStar_Tactics_Types.witness);
                         FStar_Tactics_Types.goal_ty =
                           (uu___106_5396.FStar_Tactics_Types.goal_ty);
                         FStar_Tactics_Types.opts =
                           (uu___106_5396.FStar_Tactics_Types.opts);
                         FStar_Tactics_Types.is_guard =
                           (uu___106_5396.FStar_Tactics_Types.is_guard)
                       })))
  
let (revert : Prims.unit -> Prims.unit tac) =
  fun uu____5401  ->
    let uu____5404 = cur_goal ()  in
    bind uu____5404
      (fun goal  ->
         let uu____5410 =
           FStar_TypeChecker_Env.pop_bv goal.FStar_Tactics_Types.context  in
         match uu____5410 with
         | FStar_Pervasives_Native.None  ->
             fail "Cannot revert; empty context"
         | FStar_Pervasives_Native.Some (x,env') ->
             let typ' =
               let uu____5432 =
                 FStar_Syntax_Syntax.mk_Total
                   goal.FStar_Tactics_Types.goal_ty
                  in
               FStar_Syntax_Util.arrow [(x, FStar_Pervasives_Native.None)]
                 uu____5432
                in
             let w' =
               FStar_Syntax_Util.abs [(x, FStar_Pervasives_Native.None)]
                 goal.FStar_Tactics_Types.witness
                 FStar_Pervasives_Native.None
                in
             replace_cur
               (let uu___107_5466 = goal  in
                {
                  FStar_Tactics_Types.context = env';
                  FStar_Tactics_Types.witness = w';
                  FStar_Tactics_Types.goal_ty = typ';
                  FStar_Tactics_Types.opts =
                    (uu___107_5466.FStar_Tactics_Types.opts);
                  FStar_Tactics_Types.is_guard =
                    (uu___107_5466.FStar_Tactics_Types.is_guard)
                }))
  
let (free_in :
  FStar_Syntax_Syntax.bv -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun bv  ->
    fun t  ->
      let uu____5473 = FStar_Syntax_Free.names t  in
      FStar_Util.set_mem bv uu____5473
  
let rec (clear : FStar_Syntax_Syntax.binder -> Prims.unit tac) =
  fun b  ->
    let bv = FStar_Pervasives_Native.fst b  in
    let uu____5484 = cur_goal ()  in
    bind uu____5484
      (fun goal  ->
         mlog
           (fun uu____5492  ->
              let uu____5493 = FStar_Syntax_Print.binder_to_string b  in
              let uu____5494 =
                let uu____5495 =
                  let uu____5496 =
                    FStar_TypeChecker_Env.all_binders
                      goal.FStar_Tactics_Types.context
                     in
                  FStar_All.pipe_right uu____5496 FStar_List.length  in
                FStar_All.pipe_right uu____5495 FStar_Util.string_of_int  in
              FStar_Util.print2 "Clear of (%s), env has %s binders\n"
                uu____5493 uu____5494)
           (fun uu____5507  ->
              let uu____5508 = split_env bv goal.FStar_Tactics_Types.context
                 in
              match uu____5508 with
              | FStar_Pervasives_Native.None  ->
                  fail "Cannot clear; binder not in environment"
              | FStar_Pervasives_Native.Some (e',bvs) ->
                  let rec check1 bvs1 =
                    match bvs1 with
                    | [] -> ret ()
                    | bv'::bvs2 ->
                        let uu____5553 =
                          free_in bv bv'.FStar_Syntax_Syntax.sort  in
                        if uu____5553
                        then
                          let uu____5556 =
                            let uu____5557 =
                              FStar_Syntax_Print.bv_to_string bv'  in
                            FStar_Util.format1
                              "Cannot clear; binder present in the type of %s"
                              uu____5557
                             in
                          fail uu____5556
                        else check1 bvs2
                     in
                  let uu____5559 =
                    free_in bv goal.FStar_Tactics_Types.goal_ty  in
                  if uu____5559
                  then fail "Cannot clear; binder present in goal"
                  else
                    (let uu____5563 = check1 bvs  in
                     bind uu____5563
                       (fun uu____5569  ->
                          let env' = push_bvs e' bvs  in
                          let uu____5571 =
                            new_uvar "clear.witness" env'
                              goal.FStar_Tactics_Types.goal_ty
                             in
                          bind uu____5571
                            (fun ut  ->
                               let uu____5577 =
                                 do_unify goal.FStar_Tactics_Types.context
                                   goal.FStar_Tactics_Types.witness ut
                                  in
                               bind uu____5577
                                 (fun b1  ->
                                    if b1
                                    then
                                      replace_cur
                                        (let uu___108_5586 = goal  in
                                         {
                                           FStar_Tactics_Types.context = env';
                                           FStar_Tactics_Types.witness = ut;
                                           FStar_Tactics_Types.goal_ty =
                                             (uu___108_5586.FStar_Tactics_Types.goal_ty);
                                           FStar_Tactics_Types.opts =
                                             (uu___108_5586.FStar_Tactics_Types.opts);
                                           FStar_Tactics_Types.is_guard =
                                             (uu___108_5586.FStar_Tactics_Types.is_guard)
                                         })
                                    else
                                      fail
                                        "Cannot clear; binder appears in witness"))))))
  
let (clear_top : Prims.unit -> Prims.unit tac) =
  fun uu____5592  ->
    let uu____5595 = cur_goal ()  in
    bind uu____5595
      (fun goal  ->
         let uu____5601 =
           FStar_TypeChecker_Env.pop_bv goal.FStar_Tactics_Types.context  in
         match uu____5601 with
         | FStar_Pervasives_Native.None  ->
             fail "Cannot clear; empty context"
         | FStar_Pervasives_Native.Some (x,uu____5615) ->
             let uu____5620 = FStar_Syntax_Syntax.mk_binder x  in
             clear uu____5620)
  
let (prune : Prims.string -> Prims.unit tac) =
  fun s  ->
    let uu____5628 = cur_goal ()  in
    bind uu____5628
      (fun g  ->
         let ctx = g.FStar_Tactics_Types.context  in
         let ctx' =
           FStar_TypeChecker_Env.rem_proof_ns ctx
             (FStar_Ident.path_of_text s)
            in
         let g' =
           let uu___109_5639 = g  in
           {
             FStar_Tactics_Types.context = ctx';
             FStar_Tactics_Types.witness =
               (uu___109_5639.FStar_Tactics_Types.witness);
             FStar_Tactics_Types.goal_ty =
               (uu___109_5639.FStar_Tactics_Types.goal_ty);
             FStar_Tactics_Types.opts =
               (uu___109_5639.FStar_Tactics_Types.opts);
             FStar_Tactics_Types.is_guard =
               (uu___109_5639.FStar_Tactics_Types.is_guard)
           }  in
         bind __dismiss (fun uu____5641  -> add_goals [g']))
  
let (addns : Prims.string -> Prims.unit tac) =
  fun s  ->
    let uu____5649 = cur_goal ()  in
    bind uu____5649
      (fun g  ->
         let ctx = g.FStar_Tactics_Types.context  in
         let ctx' =
           FStar_TypeChecker_Env.add_proof_ns ctx
             (FStar_Ident.path_of_text s)
            in
         let g' =
           let uu___110_5660 = g  in
           {
             FStar_Tactics_Types.context = ctx';
             FStar_Tactics_Types.witness =
               (uu___110_5660.FStar_Tactics_Types.witness);
             FStar_Tactics_Types.goal_ty =
               (uu___110_5660.FStar_Tactics_Types.goal_ty);
             FStar_Tactics_Types.opts =
               (uu___110_5660.FStar_Tactics_Types.opts);
             FStar_Tactics_Types.is_guard =
               (uu___110_5660.FStar_Tactics_Types.is_guard)
           }  in
         bind __dismiss (fun uu____5662  -> add_goals [g']))
  
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
            let uu____5694 = FStar_Syntax_Subst.compress t  in
            uu____5694.FStar_Syntax_Syntax.n  in
          let uu____5697 =
            if d = FStar_Tactics_Types.TopDown
            then
              f env
                (let uu___114_5703 = t  in
                 {
                   FStar_Syntax_Syntax.n = tn;
                   FStar_Syntax_Syntax.pos =
                     (uu___114_5703.FStar_Syntax_Syntax.pos);
                   FStar_Syntax_Syntax.vars =
                     (uu___114_5703.FStar_Syntax_Syntax.vars)
                 })
            else ret t  in
          bind uu____5697
            (fun t1  ->
               let ff = tac_fold_env d f env  in
               let tn1 =
                 let uu____5717 =
                   let uu____5718 = FStar_Syntax_Subst.compress t1  in
                   uu____5718.FStar_Syntax_Syntax.n  in
                 match uu____5717 with
                 | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
                     let uu____5745 = ff hd1  in
                     bind uu____5745
                       (fun hd2  ->
                          let fa uu____5765 =
                            match uu____5765 with
                            | (a,q) ->
                                let uu____5778 = ff a  in
                                bind uu____5778 (fun a1  -> ret (a1, q))
                             in
                          let uu____5791 = mapM fa args  in
                          bind uu____5791
                            (fun args1  ->
                               ret (FStar_Syntax_Syntax.Tm_app (hd2, args1))))
                 | FStar_Syntax_Syntax.Tm_abs (bs,t2,k) ->
                     let uu____5851 = FStar_Syntax_Subst.open_term bs t2  in
                     (match uu____5851 with
                      | (bs1,t') ->
                          let uu____5860 =
                            let uu____5863 =
                              FStar_TypeChecker_Env.push_binders env bs1  in
                            tac_fold_env d f uu____5863 t'  in
                          bind uu____5860
                            (fun t''  ->
                               let uu____5867 =
                                 let uu____5868 =
                                   let uu____5885 =
                                     FStar_Syntax_Subst.close_binders bs1  in
                                   let uu____5886 =
                                     FStar_Syntax_Subst.close bs1 t''  in
                                   (uu____5885, uu____5886, k)  in
                                 FStar_Syntax_Syntax.Tm_abs uu____5868  in
                               ret uu____5867))
                 | FStar_Syntax_Syntax.Tm_arrow (bs,k) -> ret tn
                 | FStar_Syntax_Syntax.Tm_match (hd1,brs) ->
                     let uu____5945 = ff hd1  in
                     bind uu____5945
                       (fun hd2  ->
                          let ffb br =
                            let uu____5958 =
                              FStar_Syntax_Subst.open_branch br  in
                            match uu____5958 with
                            | (pat,w,e) ->
                                let uu____5980 = ff e  in
                                bind uu____5980
                                  (fun e1  ->
                                     let br1 =
                                       FStar_Syntax_Subst.close_branch
                                         (pat, w, e1)
                                        in
                                     ret br1)
                             in
                          let uu____5993 = mapM ffb brs  in
                          bind uu____5993
                            (fun brs1  ->
                               ret (FStar_Syntax_Syntax.Tm_match (hd2, brs1))))
                 | FStar_Syntax_Syntax.Tm_let
                     ((false
                       ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl bv;
                          FStar_Syntax_Syntax.lbunivs = uu____6007;
                          FStar_Syntax_Syntax.lbtyp = uu____6008;
                          FStar_Syntax_Syntax.lbeff = uu____6009;
                          FStar_Syntax_Syntax.lbdef = def;
                          FStar_Syntax_Syntax.lbattrs = uu____6011;
                          FStar_Syntax_Syntax.lbpos = uu____6012;_}::[]),e)
                     ->
                     let lb =
                       let uu____6037 =
                         let uu____6038 = FStar_Syntax_Subst.compress t1  in
                         uu____6038.FStar_Syntax_Syntax.n  in
                       match uu____6037 with
                       | FStar_Syntax_Syntax.Tm_let
                           ((false ,lb::[]),uu____6042) -> lb
                       | uu____6055 -> failwith "impossible"  in
                     let fflb lb1 =
                       let uu____6062 = ff lb1.FStar_Syntax_Syntax.lbdef  in
                       bind uu____6062
                         (fun def1  ->
                            ret
                              (let uu___111_6068 = lb1  in
                               {
                                 FStar_Syntax_Syntax.lbname =
                                   (uu___111_6068.FStar_Syntax_Syntax.lbname);
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___111_6068.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp =
                                   (uu___111_6068.FStar_Syntax_Syntax.lbtyp);
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___111_6068.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def1;
                                 FStar_Syntax_Syntax.lbattrs =
                                   (uu___111_6068.FStar_Syntax_Syntax.lbattrs);
                                 FStar_Syntax_Syntax.lbpos =
                                   (uu___111_6068.FStar_Syntax_Syntax.lbpos)
                               }))
                        in
                     let uu____6069 = fflb lb  in
                     bind uu____6069
                       (fun lb1  ->
                          let uu____6078 =
                            let uu____6083 =
                              let uu____6084 =
                                FStar_Syntax_Syntax.mk_binder bv  in
                              [uu____6084]  in
                            FStar_Syntax_Subst.open_term uu____6083 e  in
                          match uu____6078 with
                          | (bs,e1) ->
                              let uu____6089 = ff e1  in
                              bind uu____6089
                                (fun e2  ->
                                   let e3 = FStar_Syntax_Subst.close bs e2
                                      in
                                   ret
                                     (FStar_Syntax_Syntax.Tm_let
                                        ((false, [lb1]), e3))))
                 | FStar_Syntax_Syntax.Tm_let ((true ,lbs),e) ->
                     let fflb lb =
                       let uu____6126 = ff lb.FStar_Syntax_Syntax.lbdef  in
                       bind uu____6126
                         (fun def  ->
                            ret
                              (let uu___112_6132 = lb  in
                               {
                                 FStar_Syntax_Syntax.lbname =
                                   (uu___112_6132.FStar_Syntax_Syntax.lbname);
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___112_6132.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp =
                                   (uu___112_6132.FStar_Syntax_Syntax.lbtyp);
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___112_6132.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def;
                                 FStar_Syntax_Syntax.lbattrs =
                                   (uu___112_6132.FStar_Syntax_Syntax.lbattrs);
                                 FStar_Syntax_Syntax.lbpos =
                                   (uu___112_6132.FStar_Syntax_Syntax.lbpos)
                               }))
                        in
                     let uu____6133 = FStar_Syntax_Subst.open_let_rec lbs e
                        in
                     (match uu____6133 with
                      | (lbs1,e1) ->
                          let uu____6148 = mapM fflb lbs1  in
                          bind uu____6148
                            (fun lbs2  ->
                               let uu____6160 = ff e1  in
                               bind uu____6160
                                 (fun e2  ->
                                    let uu____6168 =
                                      FStar_Syntax_Subst.close_let_rec lbs2
                                        e2
                                       in
                                    match uu____6168 with
                                    | (lbs3,e3) ->
                                        ret
                                          (FStar_Syntax_Syntax.Tm_let
                                             ((true, lbs3), e3)))))
                 | FStar_Syntax_Syntax.Tm_ascribed (t2,asc,eff) ->
                     let uu____6234 = ff t2  in
                     bind uu____6234
                       (fun t3  ->
                          ret
                            (FStar_Syntax_Syntax.Tm_ascribed (t3, asc, eff)))
                 | FStar_Syntax_Syntax.Tm_meta (t2,m) ->
                     let uu____6263 = ff t2  in
                     bind uu____6263
                       (fun t3  -> ret (FStar_Syntax_Syntax.Tm_meta (t3, m)))
                 | uu____6268 -> ret tn  in
               bind tn1
                 (fun tn2  ->
                    let t' =
                      let uu___113_6275 = t1  in
                      {
                        FStar_Syntax_Syntax.n = tn2;
                        FStar_Syntax_Syntax.pos =
                          (uu___113_6275.FStar_Syntax_Syntax.pos);
                        FStar_Syntax_Syntax.vars =
                          (uu___113_6275.FStar_Syntax_Syntax.vars)
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
            let uu____6304 = FStar_TypeChecker_TcTerm.tc_term env t  in
            match uu____6304 with
            | (t1,lcomp,g) ->
                let uu____6316 =
                  (let uu____6319 =
                     FStar_Syntax_Util.is_pure_or_ghost_lcomp lcomp  in
                   Prims.op_Negation uu____6319) ||
                    (let uu____6321 = FStar_TypeChecker_Rel.is_trivial g  in
                     Prims.op_Negation uu____6321)
                   in
                if uu____6316
                then ret t1
                else
                  (let rewrite_eq =
                     let typ = lcomp.FStar_Syntax_Syntax.res_typ  in
                     let uu____6331 = new_uvar "pointwise_rec" env typ  in
                     bind uu____6331
                       (fun ut  ->
                          log ps
                            (fun uu____6342  ->
                               let uu____6343 =
                                 FStar_Syntax_Print.term_to_string t1  in
                               let uu____6344 =
                                 FStar_Syntax_Print.term_to_string ut  in
                               FStar_Util.print2
                                 "Pointwise_rec: making equality\n\t%s ==\n\t%s\n"
                                 uu____6343 uu____6344);
                          (let uu____6345 =
                             let uu____6348 =
                               let uu____6349 =
                                 FStar_TypeChecker_TcTerm.universe_of env typ
                                  in
                               FStar_Syntax_Util.mk_eq2 uu____6349 typ t1 ut
                                in
                             add_irrelevant_goal "pointwise_rec equation" env
                               uu____6348 opts
                              in
                           bind uu____6345
                             (fun uu____6352  ->
                                let uu____6353 =
                                  bind tau
                                    (fun uu____6359  ->
                                       let ut1 =
                                         FStar_TypeChecker_Normalize.reduce_uvar_solutions
                                           env ut
                                          in
                                       log ps
                                         (fun uu____6365  ->
                                            let uu____6366 =
                                              FStar_Syntax_Print.term_to_string
                                                t1
                                               in
                                            let uu____6367 =
                                              FStar_Syntax_Print.term_to_string
                                                ut1
                                               in
                                            FStar_Util.print2
                                              "Pointwise_rec: succeeded rewriting\n\t%s to\n\t%s\n"
                                              uu____6366 uu____6367);
                                       ret ut1)
                                   in
                                focus uu____6353)))
                      in
                   let uu____6368 = trytac' rewrite_eq  in
                   bind uu____6368
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
          let uu____6516 = FStar_Syntax_Subst.compress t  in
          maybe_continue ctrl uu____6516
            (fun t1  ->
               let uu____6520 =
                 f env
                   (let uu___117_6529 = t1  in
                    {
                      FStar_Syntax_Syntax.n = (t1.FStar_Syntax_Syntax.n);
                      FStar_Syntax_Syntax.pos =
                        (uu___117_6529.FStar_Syntax_Syntax.pos);
                      FStar_Syntax_Syntax.vars =
                        (uu___117_6529.FStar_Syntax_Syntax.vars)
                    })
                  in
               bind uu____6520
                 (fun uu____6541  ->
                    match uu____6541 with
                    | (t2,ctrl1) ->
                        maybe_continue ctrl1 t2
                          (fun t3  ->
                             let uu____6560 =
                               let uu____6561 =
                                 FStar_Syntax_Subst.compress t3  in
                               uu____6561.FStar_Syntax_Syntax.n  in
                             match uu____6560 with
                             | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
                                 let uu____6594 =
                                   ctrl_tac_fold f env ctrl1 hd1  in
                                 bind uu____6594
                                   (fun uu____6619  ->
                                      match uu____6619 with
                                      | (hd2,ctrl2) ->
                                          let ctrl3 = keep_going ctrl2  in
                                          let uu____6635 =
                                            ctrl_tac_fold_args f env ctrl3
                                              args
                                             in
                                          bind uu____6635
                                            (fun uu____6662  ->
                                               match uu____6662 with
                                               | (args1,ctrl4) ->
                                                   ret
                                                     ((let uu___115_6692 = t3
                                                          in
                                                       {
                                                         FStar_Syntax_Syntax.n
                                                           =
                                                           (FStar_Syntax_Syntax.Tm_app
                                                              (hd2, args1));
                                                         FStar_Syntax_Syntax.pos
                                                           =
                                                           (uu___115_6692.FStar_Syntax_Syntax.pos);
                                                         FStar_Syntax_Syntax.vars
                                                           =
                                                           (uu___115_6692.FStar_Syntax_Syntax.vars)
                                                       }), ctrl4)))
                             | FStar_Syntax_Syntax.Tm_abs (bs,t4,k) ->
                                 let uu____6718 =
                                   FStar_Syntax_Subst.open_term bs t4  in
                                 (match uu____6718 with
                                  | (bs1,t') ->
                                      let uu____6733 =
                                        let uu____6740 =
                                          FStar_TypeChecker_Env.push_binders
                                            env bs1
                                           in
                                        ctrl_tac_fold f uu____6740 ctrl1 t'
                                         in
                                      bind uu____6733
                                        (fun uu____6758  ->
                                           match uu____6758 with
                                           | (t'',ctrl2) ->
                                               let uu____6773 =
                                                 let uu____6780 =
                                                   let uu___116_6783 = t4  in
                                                   let uu____6786 =
                                                     let uu____6787 =
                                                       let uu____6804 =
                                                         FStar_Syntax_Subst.close_binders
                                                           bs1
                                                          in
                                                       let uu____6805 =
                                                         FStar_Syntax_Subst.close
                                                           bs1 t''
                                                          in
                                                       (uu____6804,
                                                         uu____6805, k)
                                                        in
                                                     FStar_Syntax_Syntax.Tm_abs
                                                       uu____6787
                                                      in
                                                   {
                                                     FStar_Syntax_Syntax.n =
                                                       uu____6786;
                                                     FStar_Syntax_Syntax.pos
                                                       =
                                                       (uu___116_6783.FStar_Syntax_Syntax.pos);
                                                     FStar_Syntax_Syntax.vars
                                                       =
                                                       (uu___116_6783.FStar_Syntax_Syntax.vars)
                                                   }  in
                                                 (uu____6780, ctrl2)  in
                                               ret uu____6773))
                             | FStar_Syntax_Syntax.Tm_arrow (bs,k) ->
                                 ret (t3, ctrl1)
                             | uu____6838 -> ret (t3, ctrl1))))

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
              let uu____6889 = ctrl_tac_fold f env ctrl t  in
              bind uu____6889
                (fun uu____6917  ->
                   match uu____6917 with
                   | (t1,ctrl1) ->
                       let uu____6936 = ctrl_tac_fold_args f env ctrl1 ts1
                          in
                       bind uu____6936
                         (fun uu____6967  ->
                            match uu____6967 with
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
              let uu____7051 =
                let uu____7058 =
                  add_irrelevant_goal "dummy" env FStar_Syntax_Util.t_true
                    opts
                   in
                bind uu____7058
                  (fun uu____7067  ->
                     let uu____7068 = ctrl t1  in
                     bind uu____7068
                       (fun res  ->
                          let uu____7091 = trivial ()  in
                          bind uu____7091 (fun uu____7099  -> ret res)))
                 in
              bind uu____7051
                (fun uu____7115  ->
                   match uu____7115 with
                   | (should_rewrite,ctrl1) ->
                       if Prims.op_Negation should_rewrite
                       then ret (t1, ctrl1)
                       else
                         (let uu____7139 =
                            FStar_TypeChecker_TcTerm.tc_term env t1  in
                          match uu____7139 with
                          | (t2,lcomp,g) ->
                              let uu____7155 =
                                (let uu____7158 =
                                   FStar_Syntax_Util.is_pure_or_ghost_lcomp
                                     lcomp
                                    in
                                 Prims.op_Negation uu____7158) ||
                                  (let uu____7160 =
                                     FStar_TypeChecker_Rel.is_trivial g  in
                                   Prims.op_Negation uu____7160)
                                 in
                              if uu____7155
                              then ret (t2, globalStop)
                              else
                                (let typ = lcomp.FStar_Syntax_Syntax.res_typ
                                    in
                                 let uu____7175 =
                                   new_uvar "pointwise_rec" env typ  in
                                 bind uu____7175
                                   (fun ut  ->
                                      log ps
                                        (fun uu____7190  ->
                                           let uu____7191 =
                                             FStar_Syntax_Print.term_to_string
                                               t2
                                              in
                                           let uu____7192 =
                                             FStar_Syntax_Print.term_to_string
                                               ut
                                              in
                                           FStar_Util.print2
                                             "Pointwise_rec: making equality\n\t%s ==\n\t%s\n"
                                             uu____7191 uu____7192);
                                      (let uu____7193 =
                                         let uu____7196 =
                                           let uu____7197 =
                                             FStar_TypeChecker_TcTerm.universe_of
                                               env typ
                                              in
                                           FStar_Syntax_Util.mk_eq2
                                             uu____7197 typ t2 ut
                                            in
                                         add_irrelevant_goal
                                           "rewrite_rec equation" env
                                           uu____7196 opts
                                          in
                                       bind uu____7193
                                         (fun uu____7204  ->
                                            let uu____7205 =
                                              bind rewriter
                                                (fun uu____7219  ->
                                                   let ut1 =
                                                     FStar_TypeChecker_Normalize.reduce_uvar_solutions
                                                       env ut
                                                      in
                                                   log ps
                                                     (fun uu____7225  ->
                                                        let uu____7226 =
                                                          FStar_Syntax_Print.term_to_string
                                                            t2
                                                           in
                                                        let uu____7227 =
                                                          FStar_Syntax_Print.term_to_string
                                                            ut1
                                                           in
                                                        FStar_Util.print2
                                                          "rewrite_rec: succeeded rewriting\n\t%s to\n\t%s\n"
                                                          uu____7226
                                                          uu____7227);
                                                   ret (ut1, ctrl1))
                                               in
                                            focus uu____7205))))))
  
let (topdown_rewrite :
  (FStar_Syntax_Syntax.term ->
     (Prims.bool,FStar_BigInt.t) FStar_Pervasives_Native.tuple2 tac)
    -> Prims.unit tac -> Prims.unit tac)
  =
  fun ctrl  ->
    fun rewriter  ->
      bind get
        (fun ps  ->
           let uu____7271 =
             match ps.FStar_Tactics_Types.goals with
             | g::gs -> (g, gs)
             | [] -> failwith "Pointwise: no goals"  in
           match uu____7271 with
           | (g,gs) ->
               let gt1 = g.FStar_Tactics_Types.goal_ty  in
               (log ps
                  (fun uu____7308  ->
                     let uu____7309 = FStar_Syntax_Print.term_to_string gt1
                        in
                     FStar_Util.print1 "Pointwise starting with %s\n"
                       uu____7309);
                bind dismiss_all
                  (fun uu____7312  ->
                     let uu____7313 =
                       ctrl_tac_fold
                         (rewrite_rec ps ctrl rewriter
                            g.FStar_Tactics_Types.opts)
                         g.FStar_Tactics_Types.context keepGoing gt1
                        in
                     bind uu____7313
                       (fun uu____7331  ->
                          match uu____7331 with
                          | (gt',uu____7339) ->
                              (log ps
                                 (fun uu____7343  ->
                                    let uu____7344 =
                                      FStar_Syntax_Print.term_to_string gt'
                                       in
                                    FStar_Util.print1
                                      "Pointwise seems to have succeded with %s\n"
                                      uu____7344);
                               (let uu____7345 = push_goals gs  in
                                bind uu____7345
                                  (fun uu____7349  ->
                                     add_goals
                                       [(let uu___118_7351 = g  in
                                         {
                                           FStar_Tactics_Types.context =
                                             (uu___118_7351.FStar_Tactics_Types.context);
                                           FStar_Tactics_Types.witness =
                                             (uu___118_7351.FStar_Tactics_Types.witness);
                                           FStar_Tactics_Types.goal_ty = gt';
                                           FStar_Tactics_Types.opts =
                                             (uu___118_7351.FStar_Tactics_Types.opts);
                                           FStar_Tactics_Types.is_guard =
                                             (uu___118_7351.FStar_Tactics_Types.is_guard)
                                         })])))))))
  
let (pointwise :
  FStar_Tactics_Types.direction -> Prims.unit tac -> Prims.unit tac) =
  fun d  ->
    fun tau  ->
      bind get
        (fun ps  ->
           let uu____7373 =
             match ps.FStar_Tactics_Types.goals with
             | g::gs -> (g, gs)
             | [] -> failwith "Pointwise: no goals"  in
           match uu____7373 with
           | (g,gs) ->
               let gt1 = g.FStar_Tactics_Types.goal_ty  in
               (log ps
                  (fun uu____7410  ->
                     let uu____7411 = FStar_Syntax_Print.term_to_string gt1
                        in
                     FStar_Util.print1 "Pointwise starting with %s\n"
                       uu____7411);
                bind dismiss_all
                  (fun uu____7414  ->
                     let uu____7415 =
                       tac_fold_env d
                         (pointwise_rec ps tau g.FStar_Tactics_Types.opts)
                         g.FStar_Tactics_Types.context gt1
                        in
                     bind uu____7415
                       (fun gt'  ->
                          log ps
                            (fun uu____7425  ->
                               let uu____7426 =
                                 FStar_Syntax_Print.term_to_string gt'  in
                               FStar_Util.print1
                                 "Pointwise seems to have succeded with %s\n"
                                 uu____7426);
                          (let uu____7427 = push_goals gs  in
                           bind uu____7427
                             (fun uu____7431  ->
                                add_goals
                                  [(let uu___119_7433 = g  in
                                    {
                                      FStar_Tactics_Types.context =
                                        (uu___119_7433.FStar_Tactics_Types.context);
                                      FStar_Tactics_Types.witness =
                                        (uu___119_7433.FStar_Tactics_Types.witness);
                                      FStar_Tactics_Types.goal_ty = gt';
                                      FStar_Tactics_Types.opts =
                                        (uu___119_7433.FStar_Tactics_Types.opts);
                                      FStar_Tactics_Types.is_guard =
                                        (uu___119_7433.FStar_Tactics_Types.is_guard)
                                    })]))))))
  
let (trefl : Prims.unit -> Prims.unit tac) =
  fun uu____7438  ->
    let uu____7441 = cur_goal ()  in
    bind uu____7441
      (fun g  ->
         let uu____7459 =
           FStar_Syntax_Util.un_squash g.FStar_Tactics_Types.goal_ty  in
         match uu____7459 with
         | FStar_Pervasives_Native.Some t ->
             let uu____7471 = FStar_Syntax_Util.head_and_args' t  in
             (match uu____7471 with
              | (hd1,args) ->
                  let uu____7504 =
                    let uu____7517 =
                      let uu____7518 = FStar_Syntax_Util.un_uinst hd1  in
                      uu____7518.FStar_Syntax_Syntax.n  in
                    (uu____7517, args)  in
                  (match uu____7504 with
                   | (FStar_Syntax_Syntax.Tm_fvar
                      fv,uu____7532::(l,uu____7534)::(r,uu____7536)::[]) when
                       FStar_Syntax_Syntax.fv_eq_lid fv
                         FStar_Parser_Const.eq2_lid
                       ->
                       let uu____7583 =
                         do_unify g.FStar_Tactics_Types.context l r  in
                       bind uu____7583
                         (fun b  ->
                            if Prims.op_Negation b
                            then
                              let uu____7592 =
                                tts g.FStar_Tactics_Types.context l  in
                              let uu____7593 =
                                tts g.FStar_Tactics_Types.context r  in
                              fail2
                                "trefl: not a trivial equality (%s vs %s)"
                                uu____7592 uu____7593
                            else solve g FStar_Syntax_Util.exp_unit)
                   | (hd2,uu____7596) ->
                       let uu____7613 = tts g.FStar_Tactics_Types.context t
                          in
                       fail1 "trefl: not an equality (%s)" uu____7613))
         | FStar_Pervasives_Native.None  -> fail "not an irrelevant goal")
  
let (dup : Prims.unit -> Prims.unit tac) =
  fun uu____7620  ->
    let uu____7623 = cur_goal ()  in
    bind uu____7623
      (fun g  ->
         let uu____7629 =
           new_uvar "dup" g.FStar_Tactics_Types.context
             g.FStar_Tactics_Types.goal_ty
            in
         bind uu____7629
           (fun u  ->
              let g' =
                let uu___120_7636 = g  in
                {
                  FStar_Tactics_Types.context =
                    (uu___120_7636.FStar_Tactics_Types.context);
                  FStar_Tactics_Types.witness = u;
                  FStar_Tactics_Types.goal_ty =
                    (uu___120_7636.FStar_Tactics_Types.goal_ty);
                  FStar_Tactics_Types.opts =
                    (uu___120_7636.FStar_Tactics_Types.opts);
                  FStar_Tactics_Types.is_guard =
                    (uu___120_7636.FStar_Tactics_Types.is_guard)
                }  in
              bind __dismiss
                (fun uu____7639  ->
                   let uu____7640 =
                     let uu____7643 =
                       let uu____7644 =
                         FStar_TypeChecker_TcTerm.universe_of
                           g.FStar_Tactics_Types.context
                           g.FStar_Tactics_Types.goal_ty
                          in
                       FStar_Syntax_Util.mk_eq2 uu____7644
                         g.FStar_Tactics_Types.goal_ty u
                         g.FStar_Tactics_Types.witness
                        in
                     add_irrelevant_goal "dup equation"
                       g.FStar_Tactics_Types.context uu____7643
                       g.FStar_Tactics_Types.opts
                      in
                   bind uu____7640
                     (fun uu____7647  ->
                        let uu____7648 = add_goals [g']  in
                        bind uu____7648 (fun uu____7652  -> ret ())))))
  
let (flip : Prims.unit -> Prims.unit tac) =
  fun uu____7657  ->
    bind get
      (fun ps  ->
         match ps.FStar_Tactics_Types.goals with
         | g1::g2::gs ->
             set
               (let uu___121_7674 = ps  in
                {
                  FStar_Tactics_Types.main_context =
                    (uu___121_7674.FStar_Tactics_Types.main_context);
                  FStar_Tactics_Types.main_goal =
                    (uu___121_7674.FStar_Tactics_Types.main_goal);
                  FStar_Tactics_Types.all_implicits =
                    (uu___121_7674.FStar_Tactics_Types.all_implicits);
                  FStar_Tactics_Types.goals = (g2 :: g1 :: gs);
                  FStar_Tactics_Types.smt_goals =
                    (uu___121_7674.FStar_Tactics_Types.smt_goals);
                  FStar_Tactics_Types.depth =
                    (uu___121_7674.FStar_Tactics_Types.depth);
                  FStar_Tactics_Types.__dump =
                    (uu___121_7674.FStar_Tactics_Types.__dump);
                  FStar_Tactics_Types.psc =
                    (uu___121_7674.FStar_Tactics_Types.psc);
                  FStar_Tactics_Types.entry_range =
                    (uu___121_7674.FStar_Tactics_Types.entry_range);
                  FStar_Tactics_Types.guard_policy =
                    (uu___121_7674.FStar_Tactics_Types.guard_policy);
                  FStar_Tactics_Types.freshness =
                    (uu___121_7674.FStar_Tactics_Types.freshness)
                })
         | uu____7675 -> fail "flip: less than 2 goals")
  
let (later : Prims.unit -> Prims.unit tac) =
  fun uu____7682  ->
    bind get
      (fun ps  ->
         match ps.FStar_Tactics_Types.goals with
         | [] -> ret ()
         | g::gs ->
             set
               (let uu___122_7695 = ps  in
                {
                  FStar_Tactics_Types.main_context =
                    (uu___122_7695.FStar_Tactics_Types.main_context);
                  FStar_Tactics_Types.main_goal =
                    (uu___122_7695.FStar_Tactics_Types.main_goal);
                  FStar_Tactics_Types.all_implicits =
                    (uu___122_7695.FStar_Tactics_Types.all_implicits);
                  FStar_Tactics_Types.goals = (FStar_List.append gs [g]);
                  FStar_Tactics_Types.smt_goals =
                    (uu___122_7695.FStar_Tactics_Types.smt_goals);
                  FStar_Tactics_Types.depth =
                    (uu___122_7695.FStar_Tactics_Types.depth);
                  FStar_Tactics_Types.__dump =
                    (uu___122_7695.FStar_Tactics_Types.__dump);
                  FStar_Tactics_Types.psc =
                    (uu___122_7695.FStar_Tactics_Types.psc);
                  FStar_Tactics_Types.entry_range =
                    (uu___122_7695.FStar_Tactics_Types.entry_range);
                  FStar_Tactics_Types.guard_policy =
                    (uu___122_7695.FStar_Tactics_Types.guard_policy);
                  FStar_Tactics_Types.freshness =
                    (uu___122_7695.FStar_Tactics_Types.freshness)
                }))
  
let (qed : Prims.unit -> Prims.unit tac) =
  fun uu____7700  ->
    bind get
      (fun ps  ->
         match ps.FStar_Tactics_Types.goals with
         | [] -> ret ()
         | uu____7707 -> fail "Not done!")
  
let (cases :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 tac)
  =
  fun t  ->
    let uu____7725 =
      let uu____7732 = cur_goal ()  in
      bind uu____7732
        (fun g  ->
           let uu____7742 = __tc g.FStar_Tactics_Types.context t  in
           bind uu____7742
             (fun uu____7778  ->
                match uu____7778 with
                | (t1,typ,guard) ->
                    let uu____7794 = FStar_Syntax_Util.head_and_args typ  in
                    (match uu____7794 with
                     | (hd1,args) ->
                         let uu____7837 =
                           let uu____7850 =
                             let uu____7851 = FStar_Syntax_Util.un_uinst hd1
                                in
                             uu____7851.FStar_Syntax_Syntax.n  in
                           (uu____7850, args)  in
                         (match uu____7837 with
                          | (FStar_Syntax_Syntax.Tm_fvar
                             fv,(p,uu____7870)::(q,uu____7872)::[]) when
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
                                let uu___123_7910 = g  in
                                let uu____7911 =
                                  FStar_TypeChecker_Env.push_bv
                                    g.FStar_Tactics_Types.context v_p
                                   in
                                {
                                  FStar_Tactics_Types.context = uu____7911;
                                  FStar_Tactics_Types.witness =
                                    (uu___123_7910.FStar_Tactics_Types.witness);
                                  FStar_Tactics_Types.goal_ty =
                                    (uu___123_7910.FStar_Tactics_Types.goal_ty);
                                  FStar_Tactics_Types.opts =
                                    (uu___123_7910.FStar_Tactics_Types.opts);
                                  FStar_Tactics_Types.is_guard =
                                    (uu___123_7910.FStar_Tactics_Types.is_guard)
                                }  in
                              let g2 =
                                let uu___124_7913 = g  in
                                let uu____7914 =
                                  FStar_TypeChecker_Env.push_bv
                                    g.FStar_Tactics_Types.context v_q
                                   in
                                {
                                  FStar_Tactics_Types.context = uu____7914;
                                  FStar_Tactics_Types.witness =
                                    (uu___124_7913.FStar_Tactics_Types.witness);
                                  FStar_Tactics_Types.goal_ty =
                                    (uu___124_7913.FStar_Tactics_Types.goal_ty);
                                  FStar_Tactics_Types.opts =
                                    (uu___124_7913.FStar_Tactics_Types.opts);
                                  FStar_Tactics_Types.is_guard =
                                    (uu___124_7913.FStar_Tactics_Types.is_guard)
                                }  in
                              bind __dismiss
                                (fun uu____7921  ->
                                   let uu____7922 = add_goals [g1; g2]  in
                                   bind uu____7922
                                     (fun uu____7931  ->
                                        let uu____7932 =
                                          let uu____7937 =
                                            FStar_Syntax_Syntax.bv_to_name
                                              v_p
                                             in
                                          let uu____7938 =
                                            FStar_Syntax_Syntax.bv_to_name
                                              v_q
                                             in
                                          (uu____7937, uu____7938)  in
                                        ret uu____7932))
                          | uu____7943 ->
                              let uu____7956 =
                                tts g.FStar_Tactics_Types.context typ  in
                              fail1 "Not a disjunction: %s" uu____7956))))
       in
    FStar_All.pipe_left (wrap_err "cases") uu____7725
  
let (set_options : Prims.string -> Prims.unit tac) =
  fun s  ->
    let uu____7984 = cur_goal ()  in
    bind uu____7984
      (fun g  ->
         FStar_Options.push ();
         (let uu____7997 = FStar_Util.smap_copy g.FStar_Tactics_Types.opts
             in
          FStar_Options.set uu____7997);
         (let res = FStar_Options.set_options FStar_Options.Set s  in
          let opts' = FStar_Options.peek ()  in
          FStar_Options.pop ();
          (match res with
           | FStar_Getopt.Success  ->
               let g' =
                 let uu___125_8004 = g  in
                 {
                   FStar_Tactics_Types.context =
                     (uu___125_8004.FStar_Tactics_Types.context);
                   FStar_Tactics_Types.witness =
                     (uu___125_8004.FStar_Tactics_Types.witness);
                   FStar_Tactics_Types.goal_ty =
                     (uu___125_8004.FStar_Tactics_Types.goal_ty);
                   FStar_Tactics_Types.opts = opts';
                   FStar_Tactics_Types.is_guard =
                     (uu___125_8004.FStar_Tactics_Types.is_guard)
                 }  in
               replace_cur g'
           | FStar_Getopt.Error err ->
               fail2 "Setting options `%s` failed: %s" s err
           | FStar_Getopt.Help  ->
               fail1 "Setting options `%s` failed (got `Help`?)" s)))
  
let (top_env : Prims.unit -> env tac) =
  fun uu____8010  ->
    bind get
      (fun ps  -> FStar_All.pipe_left ret ps.FStar_Tactics_Types.main_context)
  
let (cur_env : Prims.unit -> env tac) =
  fun uu____8021  ->
    let uu____8024 = cur_goal ()  in
    bind uu____8024
      (fun g  -> FStar_All.pipe_left ret g.FStar_Tactics_Types.context)
  
let (cur_goal' : Prims.unit -> FStar_Syntax_Syntax.term tac) =
  fun uu____8035  ->
    let uu____8038 = cur_goal ()  in
    bind uu____8038
      (fun g  -> FStar_All.pipe_left ret g.FStar_Tactics_Types.goal_ty)
  
let (cur_witness : Prims.unit -> FStar_Syntax_Syntax.term tac) =
  fun uu____8049  ->
    let uu____8052 = cur_goal ()  in
    bind uu____8052
      (fun g  -> FStar_All.pipe_left ret g.FStar_Tactics_Types.witness)
  
let (unquote :
  FStar_Reflection_Data.typ ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac)
  =
  fun ty  ->
    fun tm  ->
      let uu____8069 =
        let uu____8072 = cur_goal ()  in
        bind uu____8072
          (fun goal  ->
             let env =
               FStar_TypeChecker_Env.set_expected_typ
                 goal.FStar_Tactics_Types.context ty
                in
             let uu____8080 = __tc env tm  in
             bind uu____8080
               (fun uu____8100  ->
                  match uu____8100 with
                  | (tm1,typ,guard) ->
                      let uu____8112 =
                        proc_guard "unquote" env guard
                          goal.FStar_Tactics_Types.opts
                         in
                      bind uu____8112 (fun uu____8116  -> ret tm1)))
         in
      FStar_All.pipe_left (wrap_err "unquote") uu____8069
  
let (uvar_env :
  env ->
    FStar_Reflection_Data.typ FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.term tac)
  =
  fun env  ->
    fun ty  ->
      let uu____8135 =
        match ty with
        | FStar_Pervasives_Native.Some ty1 -> ret ty1
        | FStar_Pervasives_Native.None  ->
            let uu____8141 =
              let uu____8142 = FStar_Syntax_Util.type_u ()  in
              FStar_All.pipe_left FStar_Pervasives_Native.fst uu____8142  in
            new_uvar "uvar_env.2" env uu____8141
         in
      bind uu____8135
        (fun typ  ->
           let uu____8154 = new_uvar "uvar_env" env typ  in
           bind uu____8154 (fun t  -> ret t))
  
let (unshelve : FStar_Syntax_Syntax.term -> Prims.unit tac) =
  fun t  ->
    let uu____8166 =
      bind get
        (fun ps  ->
           let env = ps.FStar_Tactics_Types.main_context  in
           let opts =
             match ps.FStar_Tactics_Types.goals with
             | g::uu____8177 -> g.FStar_Tactics_Types.opts
             | uu____8180 -> FStar_Options.peek ()  in
           let uu____8183 = __tc env t  in
           bind uu____8183
             (fun uu____8203  ->
                match uu____8203 with
                | (t1,typ,guard) ->
                    let uu____8215 = proc_guard "unshelve" env guard opts  in
                    bind uu____8215
                      (fun uu____8220  ->
                         let uu____8221 =
                           let uu____8224 =
                             let uu____8225 = bnorm env t1  in
                             let uu____8226 = bnorm env typ  in
                             {
                               FStar_Tactics_Types.context = env;
                               FStar_Tactics_Types.witness = uu____8225;
                               FStar_Tactics_Types.goal_ty = uu____8226;
                               FStar_Tactics_Types.opts = opts;
                               FStar_Tactics_Types.is_guard = false
                             }  in
                           [uu____8224]  in
                         add_goals uu____8221)))
       in
    FStar_All.pipe_left (wrap_err "unshelve") uu____8166
  
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
          (fun uu____8259  ->
             let uu____8260 = FStar_Options.unsafe_tactic_exec ()  in
             if uu____8260
             then
               let s =
                 FStar_Util.launch_process true "tactic_launch" prog args
                   input (fun uu____8266  -> fun uu____8267  -> false)
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
        (fun uu____8281  ->
           let uu____8282 =
             FStar_Syntax_Syntax.gen_bv nm FStar_Pervasives_Native.None t  in
           ret uu____8282)
  
let (change : FStar_Reflection_Data.typ -> Prims.unit tac) =
  fun ty  ->
    let uu____8290 =
      mlog
        (fun uu____8295  ->
           let uu____8296 = FStar_Syntax_Print.term_to_string ty  in
           FStar_Util.print1 "change: ty = %s\n" uu____8296)
        (fun uu____8299  ->
           let uu____8300 = cur_goal ()  in
           bind uu____8300
             (fun g  ->
                let uu____8306 = __tc g.FStar_Tactics_Types.context ty  in
                bind uu____8306
                  (fun uu____8326  ->
                     match uu____8326 with
                     | (ty1,uu____8336,guard) ->
                         let uu____8338 =
                           proc_guard "change" g.FStar_Tactics_Types.context
                             guard g.FStar_Tactics_Types.opts
                            in
                         bind uu____8338
                           (fun uu____8343  ->
                              let uu____8344 =
                                do_unify g.FStar_Tactics_Types.context
                                  g.FStar_Tactics_Types.goal_ty ty1
                                 in
                              bind uu____8344
                                (fun bb  ->
                                   if bb
                                   then
                                     replace_cur
                                       (let uu___126_8353 = g  in
                                        {
                                          FStar_Tactics_Types.context =
                                            (uu___126_8353.FStar_Tactics_Types.context);
                                          FStar_Tactics_Types.witness =
                                            (uu___126_8353.FStar_Tactics_Types.witness);
                                          FStar_Tactics_Types.goal_ty = ty1;
                                          FStar_Tactics_Types.opts =
                                            (uu___126_8353.FStar_Tactics_Types.opts);
                                          FStar_Tactics_Types.is_guard =
                                            (uu___126_8353.FStar_Tactics_Types.is_guard)
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
                                      let uu____8360 =
                                        do_unify
                                          g.FStar_Tactics_Types.context ng
                                          nty
                                         in
                                      bind uu____8360
                                        (fun b  ->
                                           if b
                                           then
                                             replace_cur
                                               (let uu___127_8369 = g  in
                                                {
                                                  FStar_Tactics_Types.context
                                                    =
                                                    (uu___127_8369.FStar_Tactics_Types.context);
                                                  FStar_Tactics_Types.witness
                                                    =
                                                    (uu___127_8369.FStar_Tactics_Types.witness);
                                                  FStar_Tactics_Types.goal_ty
                                                    = ty1;
                                                  FStar_Tactics_Types.opts =
                                                    (uu___127_8369.FStar_Tactics_Types.opts);
                                                  FStar_Tactics_Types.is_guard
                                                    =
                                                    (uu___127_8369.FStar_Tactics_Types.is_guard)
                                                })
                                           else fail "not convertible")))))))
       in
    FStar_All.pipe_left (wrap_err "change") uu____8290
  
let rec last : 'a . 'a Prims.list -> 'a =
  fun l  ->
    match l with
    | [] -> failwith "last: empty list"
    | x::[] -> x
    | uu____8388::xs -> last xs
  
let rec init : 'a . 'a Prims.list -> 'a Prims.list =
  fun l  ->
    match l with
    | [] -> failwith "init: empty list"
    | x::[] -> []
    | x::xs -> let uu____8413 = init xs  in x :: uu____8413
  
let rec (inspect :
  FStar_Syntax_Syntax.term -> FStar_Reflection_Data.term_view tac) =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t  in
    let t2 = FStar_Syntax_Util.un_uinst t1  in
    match t2.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_meta (t3,uu____8428) -> inspect t3
    | FStar_Syntax_Syntax.Tm_name bv ->
        FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_Var bv)
    | FStar_Syntax_Syntax.Tm_bvar bv ->
        FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_BVar bv)
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_FVar fv)
    | FStar_Syntax_Syntax.Tm_app (hd1,[]) ->
        failwith "inspect: empty arguments on Tm_app"
    | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
        let uu____8485 = last args  in
        (match uu____8485 with
         | (a,q) ->
             let q' = FStar_Reflection_Basic.inspect_aqual q  in
             let uu____8507 =
               let uu____8508 =
                 let uu____8513 =
                   let uu____8516 =
                     let uu____8517 = init args  in
                     FStar_Syntax_Syntax.mk_Tm_app hd1 uu____8517  in
                   uu____8516 FStar_Pervasives_Native.None
                     t2.FStar_Syntax_Syntax.pos
                    in
                 (uu____8513, (a, q'))  in
               FStar_Reflection_Data.Tv_App uu____8508  in
             FStar_All.pipe_left ret uu____8507)
    | FStar_Syntax_Syntax.Tm_abs ([],uu____8538,uu____8539) ->
        failwith "inspect: empty arguments on Tm_abs"
    | FStar_Syntax_Syntax.Tm_abs (bs,t3,k) ->
        let uu____8583 = FStar_Syntax_Subst.open_term bs t3  in
        (match uu____8583 with
         | (bs1,t4) ->
             (match bs1 with
              | [] -> failwith "impossible"
              | b::bs2 ->
                  let uu____8616 =
                    let uu____8617 =
                      let uu____8622 = FStar_Syntax_Util.abs bs2 t4 k  in
                      (b, uu____8622)  in
                    FStar_Reflection_Data.Tv_Abs uu____8617  in
                  FStar_All.pipe_left ret uu____8616))
    | FStar_Syntax_Syntax.Tm_type uu____8629 ->
        FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_Type ())
    | FStar_Syntax_Syntax.Tm_arrow ([],k) ->
        failwith "inspect: empty binders on arrow"
    | FStar_Syntax_Syntax.Tm_arrow uu____8649 ->
        let uu____8662 = FStar_Syntax_Util.arrow_one t2  in
        (match uu____8662 with
         | FStar_Pervasives_Native.Some (b,c) ->
             FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_Arrow (b, c))
         | FStar_Pervasives_Native.None  -> failwith "impossible")
    | FStar_Syntax_Syntax.Tm_refine (bv,t3) ->
        let b = FStar_Syntax_Syntax.mk_binder bv  in
        let uu____8692 = FStar_Syntax_Subst.open_term [b] t3  in
        (match uu____8692 with
         | (b',t4) ->
             let b1 =
               match b' with
               | b'1::[] -> b'1
               | uu____8723 -> failwith "impossible"  in
             FStar_All.pipe_left ret
               (FStar_Reflection_Data.Tv_Refine
                  ((FStar_Pervasives_Native.fst b1), t4)))
    | FStar_Syntax_Syntax.Tm_constant c ->
        let uu____8731 =
          let uu____8732 = FStar_Reflection_Basic.inspect_const c  in
          FStar_Reflection_Data.Tv_Const uu____8732  in
        FStar_All.pipe_left ret uu____8731
    | FStar_Syntax_Syntax.Tm_uvar (u,t3) ->
        let uu____8761 =
          let uu____8762 =
            let uu____8767 =
              let uu____8768 = FStar_Syntax_Unionfind.uvar_id u  in
              FStar_BigInt.of_int_fs uu____8768  in
            (uu____8767, t3)  in
          FStar_Reflection_Data.Tv_Uvar uu____8762  in
        FStar_All.pipe_left ret uu____8761
    | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),t21) ->
        if lb.FStar_Syntax_Syntax.lbunivs <> []
        then FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
        else
          (match lb.FStar_Syntax_Syntax.lbname with
           | FStar_Util.Inr uu____8796 ->
               FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
           | FStar_Util.Inl bv ->
               let b = FStar_Syntax_Syntax.mk_binder bv  in
               let uu____8801 = FStar_Syntax_Subst.open_term [b] t21  in
               (match uu____8801 with
                | (bs,t22) ->
                    let b1 =
                      match bs with
                      | b1::[] -> b1
                      | uu____8832 ->
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
           | FStar_Util.Inr uu____8864 ->
               FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
           | FStar_Util.Inl bv ->
               let uu____8868 = FStar_Syntax_Subst.open_let_rec [lb] t21  in
               (match uu____8868 with
                | (lbs,t22) ->
                    (match lbs with
                     | lb1::[] ->
                         (match lb1.FStar_Syntax_Syntax.lbname with
                          | FStar_Util.Inr uu____8888 ->
                              ret FStar_Reflection_Data.Tv_Unknown
                          | FStar_Util.Inl bv1 ->
                              FStar_All.pipe_left ret
                                (FStar_Reflection_Data.Tv_Let
                                   (true, bv1,
                                     (lb1.FStar_Syntax_Syntax.lbdef), t22)))
                     | uu____8894 ->
                         failwith
                           "impossible: open_term returned different amount of binders")))
    | FStar_Syntax_Syntax.Tm_match (t3,brs) ->
        let rec inspect_pat p =
          match p.FStar_Syntax_Syntax.v with
          | FStar_Syntax_Syntax.Pat_constant c ->
              let uu____8946 = FStar_Reflection_Basic.inspect_const c  in
              FStar_Reflection_Data.Pat_Constant uu____8946
          | FStar_Syntax_Syntax.Pat_cons (fv,ps) ->
              let uu____8965 =
                let uu____8972 =
                  FStar_List.map
                    (fun uu____8984  ->
                       match uu____8984 with
                       | (p1,uu____8992) -> inspect_pat p1) ps
                   in
                (fv, uu____8972)  in
              FStar_Reflection_Data.Pat_Cons uu____8965
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
            (fun uu___61_9046  ->
               match uu___61_9046 with
               | (pat,uu____9068,t4) ->
                   let uu____9086 = inspect_pat pat  in (uu____9086, t4))
            brs1
           in
        FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_Match (t3, brs2))
    | FStar_Syntax_Syntax.Tm_unknown  ->
        FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
    | uu____9103 ->
        ((let uu____9105 =
            let uu____9110 =
              let uu____9111 = FStar_Syntax_Print.tag_of_term t2  in
              let uu____9112 = FStar_Syntax_Print.term_to_string t2  in
              FStar_Util.format2
                "inspect: outside of expected syntax (%s, %s)\n" uu____9111
                uu____9112
               in
            (FStar_Errors.Warning_CantInspect, uu____9110)  in
          FStar_Errors.log_issue t2.FStar_Syntax_Syntax.pos uu____9105);
         FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown)
  
let (pack : FStar_Reflection_Data.term_view -> FStar_Syntax_Syntax.term tac)
  =
  fun tv  ->
    match tv with
    | FStar_Reflection_Data.Tv_Var bv ->
        let uu____9123 = FStar_Syntax_Syntax.bv_to_name bv  in
        FStar_All.pipe_left ret uu____9123
    | FStar_Reflection_Data.Tv_BVar bv ->
        let uu____9127 = FStar_Syntax_Syntax.bv_to_tm bv  in
        FStar_All.pipe_left ret uu____9127
    | FStar_Reflection_Data.Tv_FVar fv ->
        let uu____9131 = FStar_Syntax_Syntax.fv_to_tm fv  in
        FStar_All.pipe_left ret uu____9131
    | FStar_Reflection_Data.Tv_App (l,(r,q)) ->
        let q' = FStar_Reflection_Basic.pack_aqual q  in
        let uu____9142 = FStar_Syntax_Util.mk_app l [(r, q')]  in
        FStar_All.pipe_left ret uu____9142
    | FStar_Reflection_Data.Tv_Abs (b,t) ->
        let uu____9163 =
          FStar_Syntax_Util.abs [b] t FStar_Pervasives_Native.None  in
        FStar_All.pipe_left ret uu____9163
    | FStar_Reflection_Data.Tv_Arrow (b,c) ->
        let uu____9168 = FStar_Syntax_Util.arrow [b] c  in
        FStar_All.pipe_left ret uu____9168
    | FStar_Reflection_Data.Tv_Type () ->
        FStar_All.pipe_left ret FStar_Syntax_Util.ktype
    | FStar_Reflection_Data.Tv_Refine (bv,t) ->
        let uu____9189 = FStar_Syntax_Util.refine bv t  in
        FStar_All.pipe_left ret uu____9189
    | FStar_Reflection_Data.Tv_Const c ->
        let uu____9201 =
          let uu____9204 =
            let uu____9207 =
              let uu____9208 = FStar_Reflection_Basic.pack_const c  in
              FStar_Syntax_Syntax.Tm_constant uu____9208  in
            FStar_Syntax_Syntax.mk uu____9207  in
          uu____9204 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
        FStar_All.pipe_left ret uu____9201
    | FStar_Reflection_Data.Tv_Uvar (u,t) ->
        let uu____9222 =
          let uu____9225 = FStar_BigInt.to_int_fs u  in
          FStar_Syntax_Util.uvar_from_id uu____9225 t  in
        FStar_All.pipe_left ret uu____9222
    | FStar_Reflection_Data.Tv_Let (false ,bv,t1,t2) ->
        let lb =
          FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl bv) []
            bv.FStar_Syntax_Syntax.sort FStar_Parser_Const.effect_Tot_lid t1
            [] FStar_Range.dummyRange
           in
        let uu____9240 =
          let uu____9243 =
            let uu____9246 =
              let uu____9247 =
                let uu____9260 =
                  let uu____9261 =
                    let uu____9262 = FStar_Syntax_Syntax.mk_binder bv  in
                    [uu____9262]  in
                  FStar_Syntax_Subst.close uu____9261 t2  in
                ((false, [lb]), uu____9260)  in
              FStar_Syntax_Syntax.Tm_let uu____9247  in
            FStar_Syntax_Syntax.mk uu____9246  in
          uu____9243 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
        FStar_All.pipe_left ret uu____9240
    | FStar_Reflection_Data.Tv_Let (true ,bv,t1,t2) ->
        let lb =
          FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl bv) []
            bv.FStar_Syntax_Syntax.sort FStar_Parser_Const.effect_Tot_lid t1
            [] FStar_Range.dummyRange
           in
        let uu____9288 = FStar_Syntax_Subst.close_let_rec [lb] t2  in
        (match uu____9288 with
         | (lbs,body) ->
             let uu____9303 =
               FStar_Syntax_Syntax.mk
                 (FStar_Syntax_Syntax.Tm_let ((true, lbs), body))
                 FStar_Pervasives_Native.None FStar_Range.dummyRange
                in
             FStar_All.pipe_left ret uu____9303)
    | FStar_Reflection_Data.Tv_Match (t,brs) ->
        let wrap v1 =
          {
            FStar_Syntax_Syntax.v = v1;
            FStar_Syntax_Syntax.p = FStar_Range.dummyRange
          }  in
        let rec pack_pat p =
          match p with
          | FStar_Reflection_Data.Pat_Constant c ->
              let uu____9339 =
                let uu____9340 = FStar_Reflection_Basic.pack_const c  in
                FStar_Syntax_Syntax.Pat_constant uu____9340  in
              FStar_All.pipe_left wrap uu____9339
          | FStar_Reflection_Data.Pat_Cons (fv,ps) ->
              let uu____9349 =
                let uu____9350 =
                  let uu____9363 =
                    FStar_List.map
                      (fun p1  ->
                         let uu____9377 = pack_pat p1  in (uu____9377, false))
                      ps
                     in
                  (fv, uu____9363)  in
                FStar_Syntax_Syntax.Pat_cons uu____9350  in
              FStar_All.pipe_left wrap uu____9349
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
            (fun uu___62_9427  ->
               match uu___62_9427 with
               | (pat,t1) ->
                   let uu____9444 = pack_pat pat  in
                   (uu____9444, FStar_Pervasives_Native.None, t1)) brs
           in
        let brs2 = FStar_List.map FStar_Syntax_Subst.close_branch brs1  in
        let uu____9454 =
          FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_match (t, brs2))
            FStar_Pervasives_Native.None FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____9454
    | FStar_Reflection_Data.Tv_AscribedT (e,t,tacopt) ->
        let uu____9474 =
          FStar_Syntax_Syntax.mk
            (FStar_Syntax_Syntax.Tm_ascribed
               (e, ((FStar_Util.Inl t), tacopt),
                 FStar_Pervasives_Native.None)) FStar_Pervasives_Native.None
            FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____9474
    | FStar_Reflection_Data.Tv_AscribedC (e,c,tacopt) ->
        let uu____9516 =
          FStar_Syntax_Syntax.mk
            (FStar_Syntax_Syntax.Tm_ascribed
               (e, ((FStar_Util.Inr c), tacopt),
                 FStar_Pervasives_Native.None)) FStar_Pervasives_Native.None
            FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____9516
    | FStar_Reflection_Data.Tv_Unknown  ->
        let uu____9551 =
          FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
            FStar_Pervasives_Native.None FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____9551
  
let (goal_of_goal_ty :
  env ->
    FStar_Reflection_Data.typ ->
      (FStar_Tactics_Types.goal,FStar_TypeChecker_Env.guard_t)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun typ  ->
      let uu____9576 =
        FStar_TypeChecker_Util.new_implicit_var "proofstate_of_goal_ty"
          typ.FStar_Syntax_Syntax.pos env typ
         in
      match uu____9576 with
      | (u,uu____9594,g_u) ->
          let g =
            let uu____9609 = FStar_Options.peek ()  in
            {
              FStar_Tactics_Types.context = env;
              FStar_Tactics_Types.witness = u;
              FStar_Tactics_Types.goal_ty = typ;
              FStar_Tactics_Types.opts = uu____9609;
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
      let uu____9620 = goal_of_goal_ty env typ  in
      match uu____9620 with
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
  