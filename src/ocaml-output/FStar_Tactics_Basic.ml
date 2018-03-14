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
           debug_off (); ret res
         with
         | FStar_Errors.Err (uu____1039,msg) ->
             (debug_off ();
              mlog
                (fun uu____1043  ->
                   FStar_Util.print1 ">> do_unify error, (%s)\n" msg)
                (fun uu____1045  -> ret false))
         | FStar_Errors.Error (uu____1046,msg,r) ->
             (debug_off ();
              mlog
                (fun uu____1052  ->
                   let uu____1053 = FStar_Range.string_of_range r  in
                   FStar_Util.print2 ">> do_unify error, (%s) at (%s)\n" msg
                     uu____1053) (fun uu____1055  -> ret false)))
  
let (do_unify :
  env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool tac)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____1069 = __do_unify env t1 t2  in
        bind uu____1069
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
       let uu____1096 =
         let uu___68_1097 = p  in
         let uu____1098 = FStar_List.tl p.FStar_Tactics_Types.goals  in
         {
           FStar_Tactics_Types.main_context =
             (uu___68_1097.FStar_Tactics_Types.main_context);
           FStar_Tactics_Types.main_goal =
             (uu___68_1097.FStar_Tactics_Types.main_goal);
           FStar_Tactics_Types.all_implicits =
             (uu___68_1097.FStar_Tactics_Types.all_implicits);
           FStar_Tactics_Types.goals = uu____1098;
           FStar_Tactics_Types.smt_goals =
             (uu___68_1097.FStar_Tactics_Types.smt_goals);
           FStar_Tactics_Types.depth =
             (uu___68_1097.FStar_Tactics_Types.depth);
           FStar_Tactics_Types.__dump =
             (uu___68_1097.FStar_Tactics_Types.__dump);
           FStar_Tactics_Types.psc = (uu___68_1097.FStar_Tactics_Types.psc);
           FStar_Tactics_Types.entry_range =
             (uu___68_1097.FStar_Tactics_Types.entry_range);
           FStar_Tactics_Types.guard_policy =
             (uu___68_1097.FStar_Tactics_Types.guard_policy);
           FStar_Tactics_Types.freshness =
             (uu___68_1097.FStar_Tactics_Types.freshness)
         }  in
       set uu____1096)
  
let (dismiss : Prims.unit tac) =
  bind get
    (fun p  ->
       match p.FStar_Tactics_Types.goals with
       | [] -> fail "dismiss: no more goals"
       | uu____1109 -> __dismiss)
  
let (solve :
  FStar_Tactics_Types.goal -> FStar_Syntax_Syntax.term -> Prims.unit tac) =
  fun goal  ->
    fun solution  ->
      let uu____1122 = trysolve goal solution  in
      bind uu____1122
        (fun b  ->
           if b
           then __dismiss
           else
             (let uu____1130 =
                let uu____1131 =
                  tts goal.FStar_Tactics_Types.context solution  in
                let uu____1132 =
                  tts goal.FStar_Tactics_Types.context
                    goal.FStar_Tactics_Types.witness
                   in
                let uu____1133 =
                  tts goal.FStar_Tactics_Types.context
                    goal.FStar_Tactics_Types.goal_ty
                   in
                FStar_Util.format3 "%s does not solve %s : %s" uu____1131
                  uu____1132 uu____1133
                 in
              fail uu____1130))
  
let (dismiss_all : Prims.unit tac) =
  bind get
    (fun p  ->
       set
         (let uu___69_1140 = p  in
          {
            FStar_Tactics_Types.main_context =
              (uu___69_1140.FStar_Tactics_Types.main_context);
            FStar_Tactics_Types.main_goal =
              (uu___69_1140.FStar_Tactics_Types.main_goal);
            FStar_Tactics_Types.all_implicits =
              (uu___69_1140.FStar_Tactics_Types.all_implicits);
            FStar_Tactics_Types.goals = [];
            FStar_Tactics_Types.smt_goals =
              (uu___69_1140.FStar_Tactics_Types.smt_goals);
            FStar_Tactics_Types.depth =
              (uu___69_1140.FStar_Tactics_Types.depth);
            FStar_Tactics_Types.__dump =
              (uu___69_1140.FStar_Tactics_Types.__dump);
            FStar_Tactics_Types.psc = (uu___69_1140.FStar_Tactics_Types.psc);
            FStar_Tactics_Types.entry_range =
              (uu___69_1140.FStar_Tactics_Types.entry_range);
            FStar_Tactics_Types.guard_policy =
              (uu___69_1140.FStar_Tactics_Types.guard_policy);
            FStar_Tactics_Types.freshness =
              (uu___69_1140.FStar_Tactics_Types.freshness)
          }))
  
let (nwarn : Prims.int FStar_ST.ref) =
  FStar_Util.mk_ref (Prims.parse_int "0") 
let (check_valid_goal : FStar_Tactics_Types.goal -> Prims.unit) =
  fun g  ->
    let uu____1157 = FStar_Options.defensive ()  in
    if uu____1157
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
        let uu____1169 = FStar_TypeChecker_Env.pop_bv e  in
        match uu____1169 with
        | FStar_Pervasives_Native.None  -> b3
        | FStar_Pervasives_Native.Some (bv,e1) ->
            let b4 =
              b3 &&
                (FStar_TypeChecker_Env.closed e1 bv.FStar_Syntax_Syntax.sort)
               in
            aux b4 e1
         in
      let uu____1187 =
        (let uu____1190 = aux b2 env  in Prims.op_Negation uu____1190) &&
          (let uu____1192 = FStar_ST.op_Bang nwarn  in
           uu____1192 < (Prims.parse_int "5"))
         in
      (if uu____1187
       then
         ((let uu____1213 =
             let uu____1218 =
               let uu____1219 = goal_to_string g  in
               FStar_Util.format1
                 "The following goal is ill-formed. Keeping calm and carrying on...\n<%s>\n\n"
                 uu____1219
                in
             (FStar_Errors.Warning_IllFormedGoal, uu____1218)  in
           FStar_Errors.log_issue
             (g.FStar_Tactics_Types.goal_ty).FStar_Syntax_Syntax.pos
             uu____1213);
          (let uu____1220 =
             let uu____1221 = FStar_ST.op_Bang nwarn  in
             uu____1221 + (Prims.parse_int "1")  in
           FStar_ST.op_Colon_Equals nwarn uu____1220))
       else ())
    else ()
  
let (add_goals : FStar_Tactics_Types.goal Prims.list -> Prims.unit tac) =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___70_1279 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___70_1279.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___70_1279.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___70_1279.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (FStar_List.append gs p.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___70_1279.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___70_1279.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___70_1279.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___70_1279.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___70_1279.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___70_1279.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___70_1279.FStar_Tactics_Types.freshness)
            }))
  
let (add_smt_goals : FStar_Tactics_Types.goal Prims.list -> Prims.unit tac) =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___71_1297 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___71_1297.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___71_1297.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___71_1297.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___71_1297.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (FStar_List.append gs p.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___71_1297.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___71_1297.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___71_1297.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___71_1297.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___71_1297.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___71_1297.FStar_Tactics_Types.freshness)
            }))
  
let (push_goals : FStar_Tactics_Types.goal Prims.list -> Prims.unit tac) =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___72_1315 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___72_1315.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___72_1315.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___72_1315.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (FStar_List.append p.FStar_Tactics_Types.goals gs);
              FStar_Tactics_Types.smt_goals =
                (uu___72_1315.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___72_1315.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___72_1315.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___72_1315.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___72_1315.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___72_1315.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___72_1315.FStar_Tactics_Types.freshness)
            }))
  
let (push_smt_goals : FStar_Tactics_Types.goal Prims.list -> Prims.unit tac)
  =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___73_1333 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___73_1333.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___73_1333.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___73_1333.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___73_1333.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (FStar_List.append p.FStar_Tactics_Types.smt_goals gs);
              FStar_Tactics_Types.depth =
                (uu___73_1333.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___73_1333.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___73_1333.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___73_1333.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___73_1333.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___73_1333.FStar_Tactics_Types.freshness)
            }))
  
let (replace_cur : FStar_Tactics_Types.goal -> Prims.unit tac) =
  fun g  -> bind __dismiss (fun uu____1342  -> add_goals [g]) 
let (add_implicits : implicits -> Prims.unit tac) =
  fun i  ->
    bind get
      (fun p  ->
         set
           (let uu___74_1354 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___74_1354.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___74_1354.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (FStar_List.append i p.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___74_1354.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___74_1354.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___74_1354.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___74_1354.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___74_1354.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___74_1354.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___74_1354.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___74_1354.FStar_Tactics_Types.freshness)
            }))
  
let (new_uvar :
  Prims.string ->
    env -> FStar_Reflection_Data.typ -> FStar_Syntax_Syntax.term tac)
  =
  fun reason  ->
    fun env  ->
      fun typ  ->
        let uu____1380 =
          FStar_TypeChecker_Util.new_implicit_var reason
            typ.FStar_Syntax_Syntax.pos env typ
           in
        match uu____1380 with
        | (u,uu____1396,g_u) ->
            let uu____1410 =
              add_implicits g_u.FStar_TypeChecker_Env.implicits  in
            bind uu____1410 (fun uu____1414  -> ret u)
  
let (is_true : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____1418 = FStar_Syntax_Util.un_squash t  in
    match uu____1418 with
    | FStar_Pervasives_Native.Some t' ->
        let uu____1428 =
          let uu____1429 = FStar_Syntax_Subst.compress t'  in
          uu____1429.FStar_Syntax_Syntax.n  in
        (match uu____1428 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.true_lid
         | uu____1433 -> false)
    | uu____1434 -> false
  
let (is_false : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____1442 = FStar_Syntax_Util.un_squash t  in
    match uu____1442 with
    | FStar_Pervasives_Native.Some t' ->
        let uu____1452 =
          let uu____1453 = FStar_Syntax_Subst.compress t'  in
          uu____1453.FStar_Syntax_Syntax.n  in
        (match uu____1452 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.false_lid
         | uu____1457 -> false)
    | uu____1458 -> false
  
let (cur_goal : FStar_Tactics_Types.goal tac) =
  bind get
    (fun p  ->
       match p.FStar_Tactics_Types.goals with
       | [] -> fail "No more goals (1)"
       | hd1::tl1 -> ret hd1)
  
let (tadmit : Prims.unit tac) =
  let uu____1477 =
    bind cur_goal
      (fun g  ->
         (let uu____1484 =
            let uu____1489 =
              let uu____1490 = goal_to_string g  in
              FStar_Util.format1 "Tactics admitted goal <%s>\n\n" uu____1490
               in
            (FStar_Errors.Warning_TacAdmit, uu____1489)  in
          FStar_Errors.log_issue
            (g.FStar_Tactics_Types.goal_ty).FStar_Syntax_Syntax.pos
            uu____1484);
         solve g FStar_Syntax_Util.exp_unit)
     in
  FStar_All.pipe_left (wrap_err "tadmit") uu____1477 
let (fresh : FStar_BigInt.bigint tac) =
  bind get
    (fun ps  ->
       let n1 = ps.FStar_Tactics_Types.freshness  in
       let ps1 =
         let uu___75_1506 = ps  in
         {
           FStar_Tactics_Types.main_context =
             (uu___75_1506.FStar_Tactics_Types.main_context);
           FStar_Tactics_Types.main_goal =
             (uu___75_1506.FStar_Tactics_Types.main_goal);
           FStar_Tactics_Types.all_implicits =
             (uu___75_1506.FStar_Tactics_Types.all_implicits);
           FStar_Tactics_Types.goals =
             (uu___75_1506.FStar_Tactics_Types.goals);
           FStar_Tactics_Types.smt_goals =
             (uu___75_1506.FStar_Tactics_Types.smt_goals);
           FStar_Tactics_Types.depth =
             (uu___75_1506.FStar_Tactics_Types.depth);
           FStar_Tactics_Types.__dump =
             (uu___75_1506.FStar_Tactics_Types.__dump);
           FStar_Tactics_Types.psc = (uu___75_1506.FStar_Tactics_Types.psc);
           FStar_Tactics_Types.entry_range =
             (uu___75_1506.FStar_Tactics_Types.entry_range);
           FStar_Tactics_Types.guard_policy =
             (uu___75_1506.FStar_Tactics_Types.guard_policy);
           FStar_Tactics_Types.freshness = (n1 + (Prims.parse_int "1"))
         }  in
       let uu____1507 = set ps1  in
       bind uu____1507
         (fun uu____1512  ->
            let uu____1513 = FStar_BigInt.of_int_fs n1  in ret uu____1513))
  
let (ngoals : FStar_BigInt.bigint tac) =
  bind get
    (fun ps  ->
       let n1 = FStar_List.length ps.FStar_Tactics_Types.goals  in
       let uu____1523 = FStar_BigInt.of_int_fs n1  in ret uu____1523)
  
let (ngoals_smt : FStar_BigInt.bigint tac) =
  bind get
    (fun ps  ->
       let n1 = FStar_List.length ps.FStar_Tactics_Types.smt_goals  in
       let uu____1539 = FStar_BigInt.of_int_fs n1  in ret uu____1539)
  
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
            let uu____1571 = env.FStar_TypeChecker_Env.universe_of env phi
               in
            FStar_Syntax_Util.mk_squash uu____1571 phi  in
          let uu____1572 = new_uvar reason env typ  in
          bind uu____1572
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
           try
             let uu____1628 =
               (ps.FStar_Tactics_Types.main_context).FStar_TypeChecker_Env.type_of
                 e t
                in
             ret uu____1628
           with
           | FStar_Errors.Err (uu____1655,msg) ->
               let uu____1657 = tts e t  in
               let uu____1658 =
                 let uu____1659 = FStar_TypeChecker_Env.all_binders e  in
                 FStar_All.pipe_right uu____1659
                   (FStar_Syntax_Print.binders_to_string ", ")
                  in
               fail3 "Cannot type %s in context (%s). Error = (%s)"
                 uu____1657 uu____1658 msg
           | FStar_Errors.Error (uu____1666,msg,uu____1668) ->
               let uu____1669 = tts e t  in
               let uu____1670 =
                 let uu____1671 = FStar_TypeChecker_Env.all_binders e  in
                 FStar_All.pipe_right uu____1671
                   (FStar_Syntax_Print.binders_to_string ", ")
                  in
               fail3 "Cannot type %s in context (%s). Error = (%s)"
                 uu____1669 uu____1670 msg)
  
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
           (let uu___78_1705 = ps  in
            {
              FStar_Tactics_Types.main_context =
                (uu___78_1705.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___78_1705.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___78_1705.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___78_1705.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___78_1705.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___78_1705.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___78_1705.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___78_1705.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___78_1705.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy = pol;
              FStar_Tactics_Types.freshness =
                (uu___78_1705.FStar_Tactics_Types.freshness)
            }))
  
let with_policy : 'a . FStar_Tactics_Types.guard_policy -> 'a tac -> 'a tac =
  fun pol  ->
    fun t  ->
      bind get_guard_policy
        (fun old_pol  ->
           let uu____1727 = set_guard_policy pol  in
           bind uu____1727
             (fun uu____1731  ->
                bind t
                  (fun r  ->
                     let uu____1735 = set_guard_policy old_pol  in
                     bind uu____1735 (fun uu____1739  -> ret r))))
  
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
          let uu____1756 =
            let uu____1757 = FStar_TypeChecker_Rel.simplify_guard e g  in
            uu____1757.FStar_TypeChecker_Env.guard_f  in
          match uu____1756 with
          | FStar_TypeChecker_Common.Trivial  -> ret ()
          | FStar_TypeChecker_Common.NonTrivial f ->
              let uu____1761 = istrivial e f  in
              if uu____1761
              then ret ()
              else
                bind get
                  (fun ps  ->
                     match ps.FStar_Tactics_Types.guard_policy with
                     | FStar_Tactics_Types.Drop  -> ret ()
                     | FStar_Tactics_Types.Goal  ->
                         let uu____1769 = mk_irrelevant_goal reason e f opts
                            in
                         bind uu____1769
                           (fun goal  ->
                              let goal1 =
                                let uu___79_1776 = goal  in
                                {
                                  FStar_Tactics_Types.context =
                                    (uu___79_1776.FStar_Tactics_Types.context);
                                  FStar_Tactics_Types.witness =
                                    (uu___79_1776.FStar_Tactics_Types.witness);
                                  FStar_Tactics_Types.goal_ty =
                                    (uu___79_1776.FStar_Tactics_Types.goal_ty);
                                  FStar_Tactics_Types.opts =
                                    (uu___79_1776.FStar_Tactics_Types.opts);
                                  FStar_Tactics_Types.is_guard = true
                                }  in
                              push_goals [goal1])
                     | FStar_Tactics_Types.SMT  ->
                         let uu____1777 = mk_irrelevant_goal reason e f opts
                            in
                         bind uu____1777
                           (fun goal  ->
                              let goal1 =
                                let uu___80_1784 = goal  in
                                {
                                  FStar_Tactics_Types.context =
                                    (uu___80_1784.FStar_Tactics_Types.context);
                                  FStar_Tactics_Types.witness =
                                    (uu___80_1784.FStar_Tactics_Types.witness);
                                  FStar_Tactics_Types.goal_ty =
                                    (uu___80_1784.FStar_Tactics_Types.goal_ty);
                                  FStar_Tactics_Types.opts =
                                    (uu___80_1784.FStar_Tactics_Types.opts);
                                  FStar_Tactics_Types.is_guard = true
                                }  in
                              push_smt_goals [goal1])
                     | FStar_Tactics_Types.Force  ->
                         (try
                            let uu____1792 =
                              let uu____1793 =
                                let uu____1794 =
                                  FStar_TypeChecker_Rel.discharge_guard_no_smt
                                    e g
                                   in
                                FStar_All.pipe_left
                                  FStar_TypeChecker_Rel.is_trivial uu____1794
                                 in
                              Prims.op_Negation uu____1793  in
                            if uu____1792
                            then
                              mlog
                                (fun uu____1799  ->
                                   let uu____1800 =
                                     FStar_TypeChecker_Rel.guard_to_string e
                                       g
                                      in
                                   FStar_Util.print1 "guard = %s\n"
                                     uu____1800)
                                (fun uu____1802  ->
                                   fail1 "Forcing the guard failed %s)"
                                     reason)
                            else ret ()
                          with
                          | uu____1809 ->
                              mlog
                                (fun uu____1812  ->
                                   let uu____1813 =
                                     FStar_TypeChecker_Rel.guard_to_string e
                                       g
                                      in
                                   FStar_Util.print1 "guard = %s\n"
                                     uu____1813)
                                (fun uu____1815  ->
                                   fail1 "Forcing the guard failed (%s)"
                                     reason)))
  
let (tc : FStar_Syntax_Syntax.term -> FStar_Reflection_Data.typ tac) =
  fun t  ->
    let uu____1823 =
      bind cur_goal
        (fun goal  ->
           let uu____1829 = __tc goal.FStar_Tactics_Types.context t  in
           bind uu____1829
             (fun uu____1849  ->
                match uu____1849 with
                | (t1,typ,guard) ->
                    let uu____1861 =
                      proc_guard "tc" goal.FStar_Tactics_Types.context guard
                        goal.FStar_Tactics_Types.opts
                       in
                    bind uu____1861 (fun uu____1865  -> ret typ)))
       in
    FStar_All.pipe_left (wrap_err "tc") uu____1823
  
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
          let uu____1886 = mk_irrelevant_goal reason env phi opts  in
          bind uu____1886 (fun goal  -> add_goals [goal])
  
let (trivial : Prims.unit tac) =
  bind cur_goal
    (fun goal  ->
       let uu____1898 =
         istrivial goal.FStar_Tactics_Types.context
           goal.FStar_Tactics_Types.goal_ty
          in
       if uu____1898
       then solve goal FStar_Syntax_Util.exp_unit
       else
         (let uu____1902 =
            tts goal.FStar_Tactics_Types.context
              goal.FStar_Tactics_Types.goal_ty
             in
          fail1 "Not a trivial goal: %s" uu____1902))
  
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
          let uu____1923 =
            let uu____1924 = FStar_TypeChecker_Rel.simplify_guard e g  in
            uu____1924.FStar_TypeChecker_Env.guard_f  in
          match uu____1923 with
          | FStar_TypeChecker_Common.Trivial  ->
              ret FStar_Pervasives_Native.None
          | FStar_TypeChecker_Common.NonTrivial f ->
              let uu____1932 = istrivial e f  in
              if uu____1932
              then ret FStar_Pervasives_Native.None
              else
                (let uu____1940 = mk_irrelevant_goal reason e f opts  in
                 bind uu____1940
                   (fun goal  ->
                      ret
                        (FStar_Pervasives_Native.Some
                           (let uu___83_1950 = goal  in
                            {
                              FStar_Tactics_Types.context =
                                (uu___83_1950.FStar_Tactics_Types.context);
                              FStar_Tactics_Types.witness =
                                (uu___83_1950.FStar_Tactics_Types.witness);
                              FStar_Tactics_Types.goal_ty =
                                (uu___83_1950.FStar_Tactics_Types.goal_ty);
                              FStar_Tactics_Types.opts =
                                (uu___83_1950.FStar_Tactics_Types.opts);
                              FStar_Tactics_Types.is_guard = true
                            }))))
  
let (smt : Prims.unit tac) =
  bind cur_goal
    (fun g  ->
       let uu____1958 = is_irrelevant g  in
       if uu____1958
       then bind __dismiss (fun uu____1962  -> add_smt_goals [g])
       else
         (let uu____1964 =
            tts g.FStar_Tactics_Types.context g.FStar_Tactics_Types.goal_ty
             in
          fail1 "goal is not irrelevant: cannot dispatch to smt (%s)"
            uu____1964))
  
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
             let uu____2005 =
               try
                 let uu____2039 =
                   let uu____2048 = FStar_BigInt.to_int_fs n1  in
                   FStar_List.splitAt uu____2048 p.FStar_Tactics_Types.goals
                    in
                 ret uu____2039
               with | uu____2070 -> fail "divide: not enough goals"  in
             bind uu____2005
               (fun uu____2097  ->
                  match uu____2097 with
                  | (lgs,rgs) ->
                      let lp =
                        let uu___84_2123 = p  in
                        {
                          FStar_Tactics_Types.main_context =
                            (uu___84_2123.FStar_Tactics_Types.main_context);
                          FStar_Tactics_Types.main_goal =
                            (uu___84_2123.FStar_Tactics_Types.main_goal);
                          FStar_Tactics_Types.all_implicits =
                            (uu___84_2123.FStar_Tactics_Types.all_implicits);
                          FStar_Tactics_Types.goals = lgs;
                          FStar_Tactics_Types.smt_goals = [];
                          FStar_Tactics_Types.depth =
                            (uu___84_2123.FStar_Tactics_Types.depth);
                          FStar_Tactics_Types.__dump =
                            (uu___84_2123.FStar_Tactics_Types.__dump);
                          FStar_Tactics_Types.psc =
                            (uu___84_2123.FStar_Tactics_Types.psc);
                          FStar_Tactics_Types.entry_range =
                            (uu___84_2123.FStar_Tactics_Types.entry_range);
                          FStar_Tactics_Types.guard_policy =
                            (uu___84_2123.FStar_Tactics_Types.guard_policy);
                          FStar_Tactics_Types.freshness =
                            (uu___84_2123.FStar_Tactics_Types.freshness)
                        }  in
                      let rp =
                        let uu___85_2125 = p  in
                        {
                          FStar_Tactics_Types.main_context =
                            (uu___85_2125.FStar_Tactics_Types.main_context);
                          FStar_Tactics_Types.main_goal =
                            (uu___85_2125.FStar_Tactics_Types.main_goal);
                          FStar_Tactics_Types.all_implicits =
                            (uu___85_2125.FStar_Tactics_Types.all_implicits);
                          FStar_Tactics_Types.goals = rgs;
                          FStar_Tactics_Types.smt_goals = [];
                          FStar_Tactics_Types.depth =
                            (uu___85_2125.FStar_Tactics_Types.depth);
                          FStar_Tactics_Types.__dump =
                            (uu___85_2125.FStar_Tactics_Types.__dump);
                          FStar_Tactics_Types.psc =
                            (uu___85_2125.FStar_Tactics_Types.psc);
                          FStar_Tactics_Types.entry_range =
                            (uu___85_2125.FStar_Tactics_Types.entry_range);
                          FStar_Tactics_Types.guard_policy =
                            (uu___85_2125.FStar_Tactics_Types.guard_policy);
                          FStar_Tactics_Types.freshness =
                            (uu___85_2125.FStar_Tactics_Types.freshness)
                        }  in
                      let uu____2126 = set lp  in
                      bind uu____2126
                        (fun uu____2134  ->
                           bind l
                             (fun a  ->
                                bind get
                                  (fun lp'  ->
                                     let uu____2148 = set rp  in
                                     bind uu____2148
                                       (fun uu____2156  ->
                                          bind r
                                            (fun b  ->
                                               bind get
                                                 (fun rp'  ->
                                                    let p' =
                                                      let uu___86_2172 = p
                                                         in
                                                      {
                                                        FStar_Tactics_Types.main_context
                                                          =
                                                          (uu___86_2172.FStar_Tactics_Types.main_context);
                                                        FStar_Tactics_Types.main_goal
                                                          =
                                                          (uu___86_2172.FStar_Tactics_Types.main_goal);
                                                        FStar_Tactics_Types.all_implicits
                                                          =
                                                          (uu___86_2172.FStar_Tactics_Types.all_implicits);
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
                                                          (uu___86_2172.FStar_Tactics_Types.depth);
                                                        FStar_Tactics_Types.__dump
                                                          =
                                                          (uu___86_2172.FStar_Tactics_Types.__dump);
                                                        FStar_Tactics_Types.psc
                                                          =
                                                          (uu___86_2172.FStar_Tactics_Types.psc);
                                                        FStar_Tactics_Types.entry_range
                                                          =
                                                          (uu___86_2172.FStar_Tactics_Types.entry_range);
                                                        FStar_Tactics_Types.guard_policy
                                                          =
                                                          (uu___86_2172.FStar_Tactics_Types.guard_policy);
                                                        FStar_Tactics_Types.freshness
                                                          =
                                                          (uu___86_2172.FStar_Tactics_Types.freshness)
                                                      }  in
                                                    let uu____2173 = set p'
                                                       in
                                                    bind uu____2173
                                                      (fun uu____2181  ->
                                                         ret (a, b))))))))))
  
let focus : 'a . 'a tac -> 'a tac =
  fun f  ->
    let uu____2199 = divide FStar_BigInt.one f idtac  in
    bind uu____2199
      (fun uu____2212  -> match uu____2212 with | (a,()) -> ret a)
  
let rec map : 'a . 'a tac -> 'a Prims.list tac =
  fun tau  ->
    bind get
      (fun p  ->
         match p.FStar_Tactics_Types.goals with
         | [] -> ret []
         | uu____2246::uu____2247 ->
             let uu____2250 =
               let uu____2259 = map tau  in
               divide FStar_BigInt.one tau uu____2259  in
             bind uu____2250
               (fun uu____2277  ->
                  match uu____2277 with | (h,t) -> ret (h :: t)))
  
let (seq : Prims.unit tac -> Prims.unit tac -> Prims.unit tac) =
  fun t1  ->
    fun t2  ->
      let uu____2314 =
        bind t1
          (fun uu____2319  ->
             let uu____2320 = map t2  in
             bind uu____2320 (fun uu____2328  -> ret ()))
         in
      focus uu____2314
  
let (intro : FStar_Syntax_Syntax.binder tac) =
  let uu____2335 =
    bind cur_goal
      (fun goal  ->
         let uu____2344 =
           FStar_Syntax_Util.arrow_one goal.FStar_Tactics_Types.goal_ty  in
         match uu____2344 with
         | FStar_Pervasives_Native.Some (b,c) ->
             let uu____2359 =
               let uu____2360 = FStar_Syntax_Util.is_total_comp c  in
               Prims.op_Negation uu____2360  in
             if uu____2359
             then fail "Codomain is effectful"
             else
               (let env' =
                  FStar_TypeChecker_Env.push_binders
                    goal.FStar_Tactics_Types.context [b]
                   in
                let typ' = comp_to_typ c  in
                let uu____2366 = new_uvar "intro" env' typ'  in
                bind uu____2366
                  (fun u  ->
                     let uu____2372 =
                       let uu____2375 =
                         FStar_Syntax_Util.abs [b] u
                           FStar_Pervasives_Native.None
                          in
                       trysolve goal uu____2375  in
                     bind uu____2372
                       (fun bb  ->
                          if bb
                          then
                            let uu____2381 =
                              let uu____2384 =
                                let uu___89_2385 = goal  in
                                let uu____2386 = bnorm env' u  in
                                let uu____2387 = bnorm env' typ'  in
                                {
                                  FStar_Tactics_Types.context = env';
                                  FStar_Tactics_Types.witness = uu____2386;
                                  FStar_Tactics_Types.goal_ty = uu____2387;
                                  FStar_Tactics_Types.opts =
                                    (uu___89_2385.FStar_Tactics_Types.opts);
                                  FStar_Tactics_Types.is_guard =
                                    (uu___89_2385.FStar_Tactics_Types.is_guard)
                                }  in
                              replace_cur uu____2384  in
                            bind uu____2381 (fun uu____2389  -> ret b)
                          else fail "unification failed")))
         | FStar_Pervasives_Native.None  ->
             let uu____2395 =
               tts goal.FStar_Tactics_Types.context
                 goal.FStar_Tactics_Types.goal_ty
                in
             fail1 "goal is not an arrow (%s)" uu____2395)
     in
  FStar_All.pipe_left (wrap_err "intro") uu____2335 
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
       (let uu____2426 =
          FStar_Syntax_Util.arrow_one goal.FStar_Tactics_Types.goal_ty  in
        match uu____2426 with
        | FStar_Pervasives_Native.Some (b,c) ->
            let uu____2445 =
              let uu____2446 = FStar_Syntax_Util.is_total_comp c  in
              Prims.op_Negation uu____2446  in
            if uu____2445
            then fail "Codomain is effectful"
            else
              (let bv =
                 FStar_Syntax_Syntax.gen_bv "__recf"
                   FStar_Pervasives_Native.None
                   goal.FStar_Tactics_Types.goal_ty
                  in
               let bs =
                 let uu____2462 = FStar_Syntax_Syntax.mk_binder bv  in
                 [uu____2462; b]  in
               let env' =
                 FStar_TypeChecker_Env.push_binders
                   goal.FStar_Tactics_Types.context bs
                  in
               let uu____2464 =
                 let uu____2467 = comp_to_typ c  in
                 new_uvar "intro_rec" env' uu____2467  in
               bind uu____2464
                 (fun u  ->
                    let lb =
                      let uu____2482 =
                        FStar_Syntax_Util.abs [b] u
                          FStar_Pervasives_Native.None
                         in
                      FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl bv) []
                        goal.FStar_Tactics_Types.goal_ty
                        FStar_Parser_Const.effect_Tot_lid uu____2482 []
                        FStar_Range.dummyRange
                       in
                    let body = FStar_Syntax_Syntax.bv_to_name bv  in
                    let uu____2488 =
                      FStar_Syntax_Subst.close_let_rec [lb] body  in
                    match uu____2488 with
                    | (lbs,body1) ->
                        let tm =
                          FStar_Syntax_Syntax.mk
                            (FStar_Syntax_Syntax.Tm_let ((true, lbs), body1))
                            FStar_Pervasives_Native.None
                            (goal.FStar_Tactics_Types.witness).FStar_Syntax_Syntax.pos
                           in
                        let uu____2518 = trysolve goal tm  in
                        bind uu____2518
                          (fun bb  ->
                             if bb
                             then
                               let uu____2534 =
                                 let uu____2537 =
                                   let uu___90_2538 = goal  in
                                   let uu____2539 = bnorm env' u  in
                                   let uu____2540 =
                                     let uu____2541 = comp_to_typ c  in
                                     bnorm env' uu____2541  in
                                   {
                                     FStar_Tactics_Types.context = env';
                                     FStar_Tactics_Types.witness = uu____2539;
                                     FStar_Tactics_Types.goal_ty = uu____2540;
                                     FStar_Tactics_Types.opts =
                                       (uu___90_2538.FStar_Tactics_Types.opts);
                                     FStar_Tactics_Types.is_guard =
                                       (uu___90_2538.FStar_Tactics_Types.is_guard)
                                   }  in
                                 replace_cur uu____2537  in
                               bind uu____2534
                                 (fun uu____2548  ->
                                    let uu____2549 =
                                      let uu____2554 =
                                        FStar_Syntax_Syntax.mk_binder bv  in
                                      (uu____2554, b)  in
                                    ret uu____2549)
                             else fail "intro_rec: unification failed")))
        | FStar_Pervasives_Native.None  ->
            let uu____2568 =
              tts goal.FStar_Tactics_Types.context
                goal.FStar_Tactics_Types.goal_ty
               in
            fail1 "intro_rec: goal is not an arrow (%s)" uu____2568))
  
let (norm : FStar_Syntax_Embeddings.norm_step Prims.list -> Prims.unit tac) =
  fun s  ->
    bind cur_goal
      (fun goal  ->
         mlog
           (fun uu____2588  ->
              let uu____2589 =
                FStar_Syntax_Print.term_to_string
                  goal.FStar_Tactics_Types.witness
                 in
              FStar_Util.print1 "norm: witness = %s\n" uu____2589)
           (fun uu____2594  ->
              let steps =
                let uu____2598 = FStar_TypeChecker_Normalize.tr_norm_steps s
                   in
                FStar_List.append
                  [FStar_TypeChecker_Normalize.Reify;
                  FStar_TypeChecker_Normalize.UnfoldTac] uu____2598
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
                (let uu___91_2605 = goal  in
                 {
                   FStar_Tactics_Types.context =
                     (uu___91_2605.FStar_Tactics_Types.context);
                   FStar_Tactics_Types.witness = w;
                   FStar_Tactics_Types.goal_ty = t;
                   FStar_Tactics_Types.opts =
                     (uu___91_2605.FStar_Tactics_Types.opts);
                   FStar_Tactics_Types.is_guard =
                     (uu___91_2605.FStar_Tactics_Types.is_guard)
                 })))
  
let (norm_term_env :
  env ->
    FStar_Syntax_Embeddings.norm_step Prims.list ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac)
  =
  fun e  ->
    fun s  ->
      fun t  ->
        let uu____2623 =
          mlog
            (fun uu____2628  ->
               let uu____2629 = FStar_Syntax_Print.term_to_string t  in
               FStar_Util.print1 "norm_term: tm = %s\n" uu____2629)
            (fun uu____2631  ->
               bind get
                 (fun ps  ->
                    let opts =
                      match ps.FStar_Tactics_Types.goals with
                      | g::uu____2637 -> g.FStar_Tactics_Types.opts
                      | uu____2640 -> FStar_Options.peek ()  in
                    mlog
                      (fun uu____2645  ->
                         let uu____2646 =
                           tts ps.FStar_Tactics_Types.main_context t  in
                         FStar_Util.print1 "norm_term_env: t = %s\n"
                           uu____2646)
                      (fun uu____2649  ->
                         let uu____2650 = __tc e t  in
                         bind uu____2650
                           (fun uu____2671  ->
                              match uu____2671 with
                              | (t1,uu____2681,uu____2682) ->
                                  let steps =
                                    let uu____2686 =
                                      FStar_TypeChecker_Normalize.tr_norm_steps
                                        s
                                       in
                                    FStar_List.append
                                      [FStar_TypeChecker_Normalize.Reify;
                                      FStar_TypeChecker_Normalize.UnfoldTac]
                                      uu____2686
                                     in
                                  let t2 =
                                    normalize steps
                                      ps.FStar_Tactics_Types.main_context t1
                                     in
                                  ret t2))))
           in
        FStar_All.pipe_left (wrap_err "norm_term") uu____2623
  
let (refine_intro : Prims.unit tac) =
  let uu____2698 =
    bind cur_goal
      (fun g  ->
         let uu____2705 =
           FStar_TypeChecker_Rel.base_and_refinement
             g.FStar_Tactics_Types.context g.FStar_Tactics_Types.goal_ty
            in
         match uu____2705 with
         | (uu____2718,FStar_Pervasives_Native.None ) ->
             fail "not a refinement"
         | (t,FStar_Pervasives_Native.Some (bv,phi)) ->
             let g1 =
               let uu___92_2743 = g  in
               {
                 FStar_Tactics_Types.context =
                   (uu___92_2743.FStar_Tactics_Types.context);
                 FStar_Tactics_Types.witness =
                   (uu___92_2743.FStar_Tactics_Types.witness);
                 FStar_Tactics_Types.goal_ty = t;
                 FStar_Tactics_Types.opts =
                   (uu___92_2743.FStar_Tactics_Types.opts);
                 FStar_Tactics_Types.is_guard =
                   (uu___92_2743.FStar_Tactics_Types.is_guard)
               }  in
             let uu____2744 =
               let uu____2749 =
                 let uu____2754 =
                   let uu____2755 = FStar_Syntax_Syntax.mk_binder bv  in
                   [uu____2755]  in
                 FStar_Syntax_Subst.open_term uu____2754 phi  in
               match uu____2749 with
               | (bvs,phi1) ->
                   let uu____2762 =
                     let uu____2763 = FStar_List.hd bvs  in
                     FStar_Pervasives_Native.fst uu____2763  in
                   (uu____2762, phi1)
                in
             (match uu____2744 with
              | (bv1,phi1) ->
                  let uu____2776 =
                    let uu____2779 =
                      FStar_Syntax_Subst.subst
                        [FStar_Syntax_Syntax.NT
                           (bv1, (g.FStar_Tactics_Types.witness))] phi1
                       in
                    mk_irrelevant_goal "refine_intro refinement"
                      g.FStar_Tactics_Types.context uu____2779
                      g.FStar_Tactics_Types.opts
                     in
                  bind uu____2776
                    (fun g2  ->
                       bind __dismiss (fun uu____2783  -> add_goals [g1; g2]))))
     in
  FStar_All.pipe_left (wrap_err "refine_intro") uu____2698 
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
           let uu____2804 = __tc env t  in
           bind uu____2804
             (fun uu____2824  ->
                match uu____2824 with
                | (t1,typ,guard) ->
                    let uu____2836 =
                      proc_guard "__exact typing"
                        goal.FStar_Tactics_Types.context guard
                        goal.FStar_Tactics_Types.opts
                       in
                    bind uu____2836
                      (fun uu____2840  ->
                         mlog
                           (fun uu____2844  ->
                              let uu____2845 =
                                tts goal.FStar_Tactics_Types.context typ  in
                              let uu____2846 =
                                tts goal.FStar_Tactics_Types.context
                                  goal.FStar_Tactics_Types.goal_ty
                                 in
                              FStar_Util.print2 "exact: unifying %s and %s\n"
                                uu____2845 uu____2846)
                           (fun uu____2849  ->
                              let uu____2850 =
                                do_unify goal.FStar_Tactics_Types.context typ
                                  goal.FStar_Tactics_Types.goal_ty
                                 in
                              bind uu____2850
                                (fun b  ->
                                   if b
                                   then solve goal t1
                                   else
                                     (let uu____2858 =
                                        tts goal.FStar_Tactics_Types.context
                                          t1
                                         in
                                      let uu____2859 =
                                        tts goal.FStar_Tactics_Types.context
                                          typ
                                         in
                                      let uu____2860 =
                                        tts goal.FStar_Tactics_Types.context
                                          goal.FStar_Tactics_Types.goal_ty
                                         in
                                      let uu____2861 =
                                        tts goal.FStar_Tactics_Types.context
                                          goal.FStar_Tactics_Types.witness
                                         in
                                      fail4
                                        "%s : %s does not exactly solve the goal %s (witness = %s)"
                                        uu____2858 uu____2859 uu____2860
                                        uu____2861))))))
  
let (t_exact : Prims.bool -> FStar_Syntax_Syntax.term -> Prims.unit tac) =
  fun set_expected_typ1  ->
    fun tm  ->
      let uu____2872 =
        mlog
          (fun uu____2877  ->
             let uu____2878 = FStar_Syntax_Print.term_to_string tm  in
             FStar_Util.print1 "t_exact: tm = %s\n" uu____2878)
          (fun uu____2881  ->
             let uu____2882 =
               let uu____2889 = __exact_now set_expected_typ1 tm  in
               trytac' uu____2889  in
             bind uu____2882
               (fun uu___58_2898  ->
                  match uu___58_2898 with
                  | FStar_Util.Inr r -> ret ()
                  | FStar_Util.Inl e ->
                      let uu____2907 =
                        let uu____2914 =
                          let uu____2917 =
                            norm [FStar_Syntax_Embeddings.Delta]  in
                          bind uu____2917
                            (fun uu____2921  ->
                               bind refine_intro
                                 (fun uu____2923  ->
                                    __exact_now set_expected_typ1 tm))
                           in
                        trytac' uu____2914  in
                      bind uu____2907
                        (fun uu___57_2930  ->
                           match uu___57_2930 with
                           | FStar_Util.Inr r -> ret ()
                           | FStar_Util.Inl uu____2938 -> fail e)))
         in
      FStar_All.pipe_left (wrap_err "exact") uu____2872
  
let (uvar_free_in_goal :
  FStar_Syntax_Syntax.uvar -> FStar_Tactics_Types.goal -> Prims.bool) =
  fun u  ->
    fun g  ->
      if g.FStar_Tactics_Types.is_guard
      then false
      else
        (let free_uvars =
           let uu____2953 =
             let uu____2960 =
               FStar_Syntax_Free.uvars g.FStar_Tactics_Types.goal_ty  in
             FStar_Util.set_elements uu____2960  in
           FStar_List.map FStar_Pervasives_Native.fst uu____2953  in
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
          let uu____3020 = f x  in
          bind uu____3020
            (fun y  ->
               let uu____3028 = mapM f xs  in
               bind uu____3028 (fun ys  -> ret (y :: ys)))
  
exception NoUnif 
let (uu___is_NoUnif : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with | NoUnif  -> true | uu____3046 -> false
  
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
               (fun uu____3064  ->
                  let uu____3065 = FStar_Syntax_Print.term_to_string tm  in
                  FStar_Util.print1 ">>> Calling __exact(%s)\n" uu____3065)
               (fun uu____3068  ->
                  let uu____3069 =
                    let uu____3074 =
                      let uu____3077 = t_exact false tm  in
                      with_policy FStar_Tactics_Types.Force uu____3077  in
                    trytac_exn uu____3074  in
                  bind uu____3069
                    (fun uu___59_3084  ->
                       match uu___59_3084 with
                       | FStar_Pervasives_Native.Some r -> ret ()
                       | FStar_Pervasives_Native.None  ->
                           mlog
                             (fun uu____3092  ->
                                let uu____3093 =
                                  FStar_Syntax_Print.term_to_string typ  in
                                FStar_Util.print1 ">>> typ = %s\n" uu____3093)
                             (fun uu____3096  ->
                                let uu____3097 =
                                  FStar_Syntax_Util.arrow_one typ  in
                                match uu____3097 with
                                | FStar_Pervasives_Native.None  ->
                                    FStar_Exn.raise NoUnif
                                | FStar_Pervasives_Native.Some ((bv,aq),c) ->
                                    mlog
                                      (fun uu____3129  ->
                                         let uu____3130 =
                                           FStar_Syntax_Print.binder_to_string
                                             (bv, aq)
                                            in
                                         FStar_Util.print1
                                           "__apply: pushing binder %s\n"
                                           uu____3130)
                                      (fun uu____3133  ->
                                         let uu____3134 =
                                           let uu____3135 =
                                             FStar_Syntax_Util.is_total_comp
                                               c
                                              in
                                           Prims.op_Negation uu____3135  in
                                         if uu____3134
                                         then
                                           fail "apply: not total codomain"
                                         else
                                           (let uu____3139 =
                                              new_uvar "apply"
                                                goal.FStar_Tactics_Types.context
                                                bv.FStar_Syntax_Syntax.sort
                                               in
                                            bind uu____3139
                                              (fun u  ->
                                                 let tm' =
                                                   FStar_Syntax_Syntax.mk_Tm_app
                                                     tm [(u, aq)]
                                                     FStar_Pervasives_Native.None
                                                     tm.FStar_Syntax_Syntax.pos
                                                    in
                                                 let typ' =
                                                   let uu____3159 =
                                                     comp_to_typ c  in
                                                   FStar_All.pipe_left
                                                     (FStar_Syntax_Subst.subst
                                                        [FStar_Syntax_Syntax.NT
                                                           (bv, u)])
                                                     uu____3159
                                                    in
                                                 let uu____3160 =
                                                   __apply uopt tm' typ'  in
                                                 bind uu____3160
                                                   (fun uu____3168  ->
                                                      let u1 =
                                                        bnorm
                                                          goal.FStar_Tactics_Types.context
                                                          u
                                                         in
                                                      let uu____3170 =
                                                        let uu____3171 =
                                                          let uu____3174 =
                                                            let uu____3175 =
                                                              FStar_Syntax_Util.head_and_args
                                                                u1
                                                               in
                                                            FStar_Pervasives_Native.fst
                                                              uu____3175
                                                             in
                                                          FStar_Syntax_Subst.compress
                                                            uu____3174
                                                           in
                                                        uu____3171.FStar_Syntax_Syntax.n
                                                         in
                                                      match uu____3170 with
                                                      | FStar_Syntax_Syntax.Tm_uvar
                                                          (uvar,uu____3203)
                                                          ->
                                                          bind get
                                                            (fun ps  ->
                                                               let uu____3231
                                                                 =
                                                                 uopt &&
                                                                   (uvar_free
                                                                    uvar ps)
                                                                  in
                                                               if uu____3231
                                                               then ret ()
                                                               else
                                                                 (let uu____3235
                                                                    =
                                                                    let uu____3238
                                                                    =
                                                                    let uu___93_3239
                                                                    = goal
                                                                     in
                                                                    let uu____3240
                                                                    =
                                                                    bnorm
                                                                    goal.FStar_Tactics_Types.context
                                                                    u1  in
                                                                    let uu____3241
                                                                    =
                                                                    bnorm
                                                                    goal.FStar_Tactics_Types.context
                                                                    bv.FStar_Syntax_Syntax.sort
                                                                     in
                                                                    {
                                                                    FStar_Tactics_Types.context
                                                                    =
                                                                    (uu___93_3239.FStar_Tactics_Types.context);
                                                                    FStar_Tactics_Types.witness
                                                                    =
                                                                    uu____3240;
                                                                    FStar_Tactics_Types.goal_ty
                                                                    =
                                                                    uu____3241;
                                                                    FStar_Tactics_Types.opts
                                                                    =
                                                                    (uu___93_3239.FStar_Tactics_Types.opts);
                                                                    FStar_Tactics_Types.is_guard
                                                                    = false
                                                                    }  in
                                                                    [uu____3238]
                                                                     in
                                                                  add_goals
                                                                    uu____3235))
                                                      | t -> ret ()))))))))
  
let try_unif : 'a . 'a tac -> 'a tac -> 'a tac =
  fun t  ->
    fun t'  -> mk_tac (fun ps  -> try run t ps with | NoUnif  -> run t' ps)
  
let (apply : Prims.bool -> FStar_Syntax_Syntax.term -> Prims.unit tac) =
  fun uopt  ->
    fun tm  ->
      let uu____3287 =
        mlog
          (fun uu____3292  ->
             let uu____3293 = FStar_Syntax_Print.term_to_string tm  in
             FStar_Util.print1 "apply: tm = %s\n" uu____3293)
          (fun uu____3295  ->
             bind cur_goal
               (fun goal  ->
                  let uu____3299 = __tc goal.FStar_Tactics_Types.context tm
                     in
                  bind uu____3299
                    (fun uu____3321  ->
                       match uu____3321 with
                       | (tm1,typ,guard) ->
                           let typ1 =
                             bnorm goal.FStar_Tactics_Types.context typ  in
                           let uu____3334 =
                             let uu____3337 =
                               let uu____3340 = __apply uopt tm1 typ1  in
                               bind uu____3340
                                 (fun uu____3344  ->
                                    proc_guard "apply guard"
                                      goal.FStar_Tactics_Types.context guard
                                      goal.FStar_Tactics_Types.opts)
                                in
                             focus uu____3337  in
                           let uu____3345 =
                             let uu____3348 =
                               tts goal.FStar_Tactics_Types.context tm1  in
                             let uu____3349 =
                               tts goal.FStar_Tactics_Types.context typ1  in
                             let uu____3350 =
                               tts goal.FStar_Tactics_Types.context
                                 goal.FStar_Tactics_Types.goal_ty
                                in
                             fail3
                               "Cannot instantiate %s (of type %s) to match goal (%s)"
                               uu____3348 uu____3349 uu____3350
                              in
                           try_unif uu____3334 uu____3345)))
         in
      FStar_All.pipe_left (wrap_err "apply") uu____3287
  
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
      let uu____3377 =
        match ct.FStar_Syntax_Syntax.effect_args with
        | pre::post::uu____3396 ->
            ((FStar_Pervasives_Native.fst pre),
              (FStar_Pervasives_Native.fst post))
        | uu____3437 -> failwith "apply_lemma: impossible: not a lemma"  in
      match uu____3377 with
      | (pre,post) ->
          let post1 =
            let uu____3473 =
              let uu____3482 =
                FStar_Syntax_Syntax.as_arg FStar_Syntax_Util.exp_unit  in
              [uu____3482]  in
            FStar_Syntax_Util.mk_app post uu____3473  in
          FStar_Pervasives_Native.Some (pre, post1)
    else
      if FStar_Syntax_Util.is_pure_effect ct.FStar_Syntax_Syntax.effect_name
      then
        (let uu____3502 =
           FStar_Syntax_Util.un_squash ct.FStar_Syntax_Syntax.result_typ  in
         FStar_Util.map_opt uu____3502
           (fun post  -> (FStar_Syntax_Util.t_true, post)))
      else FStar_Pervasives_Native.None
  
let (apply_lemma : FStar_Syntax_Syntax.term -> Prims.unit tac) =
  fun tm  ->
    let uu____3533 =
      let uu____3536 =
        mlog
          (fun uu____3541  ->
             let uu____3542 = FStar_Syntax_Print.term_to_string tm  in
             FStar_Util.print1 "apply_lemma: tm = %s\n" uu____3542)
          (fun uu____3545  ->
             let is_unit_t t =
               let uu____3550 =
                 let uu____3551 = FStar_Syntax_Subst.compress t  in
                 uu____3551.FStar_Syntax_Syntax.n  in
               match uu____3550 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.unit_lid
                   -> true
               | uu____3555 -> false  in
             bind cur_goal
               (fun goal  ->
                  let uu____3559 = __tc goal.FStar_Tactics_Types.context tm
                     in
                  bind uu____3559
                    (fun uu____3582  ->
                       match uu____3582 with
                       | (tm1,t,guard) ->
                           let uu____3594 =
                             FStar_Syntax_Util.arrow_formals_comp t  in
                           (match uu____3594 with
                            | (bs,comp) ->
                                let uu____3621 = lemma_or_sq comp  in
                                (match uu____3621 with
                                 | FStar_Pervasives_Native.None  ->
                                     fail "not a lemma or squashed function"
                                 | FStar_Pervasives_Native.Some (pre,post) ->
                                     let uu____3640 =
                                       FStar_List.fold_left
                                         (fun uu____3686  ->
                                            fun uu____3687  ->
                                              match (uu____3686, uu____3687)
                                              with
                                              | ((uvs,guard1,subst1),(b,aq))
                                                  ->
                                                  let b_t =
                                                    FStar_Syntax_Subst.subst
                                                      subst1
                                                      b.FStar_Syntax_Syntax.sort
                                                     in
                                                  let uu____3790 =
                                                    is_unit_t b_t  in
                                                  if uu____3790
                                                  then
                                                    (((FStar_Syntax_Util.exp_unit,
                                                        aq) :: uvs), guard1,
                                                      ((FStar_Syntax_Syntax.NT
                                                          (b,
                                                            FStar_Syntax_Util.exp_unit))
                                                      :: subst1))
                                                  else
                                                    (let uu____3828 =
                                                       FStar_TypeChecker_Util.new_implicit_var
                                                         "apply_lemma"
                                                         (goal.FStar_Tactics_Types.goal_ty).FStar_Syntax_Syntax.pos
                                                         goal.FStar_Tactics_Types.context
                                                         b_t
                                                        in
                                                     match uu____3828 with
                                                     | (u,uu____3858,g_u) ->
                                                         let uu____3872 =
                                                           FStar_TypeChecker_Rel.conj_guard
                                                             guard1 g_u
                                                            in
                                                         (((u, aq) :: uvs),
                                                           uu____3872,
                                                           ((FStar_Syntax_Syntax.NT
                                                               (b, u)) ::
                                                           subst1))))
                                         ([], guard, []) bs
                                        in
                                     (match uu____3640 with
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
                                          let uu____3943 =
                                            let uu____3946 =
                                              FStar_Syntax_Util.mk_squash
                                                FStar_Syntax_Syntax.U_zero
                                                post1
                                               in
                                            do_unify
                                              goal.FStar_Tactics_Types.context
                                              uu____3946
                                              goal.FStar_Tactics_Types.goal_ty
                                             in
                                          bind uu____3943
                                            (fun b  ->
                                               if Prims.op_Negation b
                                               then
                                                 let uu____3954 =
                                                   tts
                                                     goal.FStar_Tactics_Types.context
                                                     tm1
                                                    in
                                                 let uu____3955 =
                                                   let uu____3956 =
                                                     FStar_Syntax_Util.mk_squash
                                                       FStar_Syntax_Syntax.U_zero
                                                       post1
                                                      in
                                                   tts
                                                     goal.FStar_Tactics_Types.context
                                                     uu____3956
                                                    in
                                                 let uu____3957 =
                                                   tts
                                                     goal.FStar_Tactics_Types.context
                                                     goal.FStar_Tactics_Types.goal_ty
                                                    in
                                                 fail3
                                                   "Cannot instantiate lemma %s (with postcondition: %s) to match goal (%s)"
                                                   uu____3954 uu____3955
                                                   uu____3957
                                               else
                                                 (let uu____3959 =
                                                    add_implicits
                                                      implicits.FStar_TypeChecker_Env.implicits
                                                     in
                                                  bind uu____3959
                                                    (fun uu____3964  ->
                                                       let uu____3965 =
                                                         solve goal
                                                           FStar_Syntax_Util.exp_unit
                                                          in
                                                       bind uu____3965
                                                         (fun uu____3973  ->
                                                            let is_free_uvar
                                                              uv t1 =
                                                              let free_uvars
                                                                =
                                                                let uu____3984
                                                                  =
                                                                  let uu____3991
                                                                    =
                                                                    FStar_Syntax_Free.uvars
                                                                    t1  in
                                                                  FStar_Util.set_elements
                                                                    uu____3991
                                                                   in
                                                                FStar_List.map
                                                                  FStar_Pervasives_Native.fst
                                                                  uu____3984
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
                                                              let uu____4032
                                                                =
                                                                FStar_Syntax_Util.head_and_args
                                                                  t1
                                                                 in
                                                              match uu____4032
                                                              with
                                                              | (hd1,uu____4048)
                                                                  ->
                                                                  (match 
                                                                    hd1.FStar_Syntax_Syntax.n
                                                                   with
                                                                   | 
                                                                   FStar_Syntax_Syntax.Tm_uvar
                                                                    (uv,uu____4070)
                                                                    ->
                                                                    appears
                                                                    uv goals
                                                                   | 
                                                                   uu____4095
                                                                    -> false)
                                                               in
                                                            let uu____4096 =
                                                              FStar_All.pipe_right
                                                                implicits.FStar_TypeChecker_Env.implicits
                                                                (mapM
                                                                   (fun
                                                                    uu____4168
                                                                     ->
                                                                    match uu____4168
                                                                    with
                                                                    | 
                                                                    (_msg,env,_uvar,term,typ,uu____4196)
                                                                    ->
                                                                    let uu____4197
                                                                    =
                                                                    FStar_Syntax_Util.head_and_args
                                                                    term  in
                                                                    (match uu____4197
                                                                    with
                                                                    | 
                                                                    (hd1,uu____4223)
                                                                    ->
                                                                    let uu____4244
                                                                    =
                                                                    let uu____4245
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    hd1  in
                                                                    uu____4245.FStar_Syntax_Syntax.n
                                                                     in
                                                                    (match uu____4244
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Tm_uvar
                                                                    uu____4258
                                                                    ->
                                                                    let uu____4275
                                                                    =
                                                                    let uu____4284
                                                                    =
                                                                    let uu____4287
                                                                    =
                                                                    let uu___96_4288
                                                                    = goal
                                                                     in
                                                                    let uu____4289
                                                                    =
                                                                    bnorm
                                                                    goal.FStar_Tactics_Types.context
                                                                    term  in
                                                                    let uu____4290
                                                                    =
                                                                    bnorm
                                                                    goal.FStar_Tactics_Types.context
                                                                    typ  in
                                                                    {
                                                                    FStar_Tactics_Types.context
                                                                    =
                                                                    (uu___96_4288.FStar_Tactics_Types.context);
                                                                    FStar_Tactics_Types.witness
                                                                    =
                                                                    uu____4289;
                                                                    FStar_Tactics_Types.goal_ty
                                                                    =
                                                                    uu____4290;
                                                                    FStar_Tactics_Types.opts
                                                                    =
                                                                    (uu___96_4288.FStar_Tactics_Types.opts);
                                                                    FStar_Tactics_Types.is_guard
                                                                    =
                                                                    (uu___96_4288.FStar_Tactics_Types.is_guard)
                                                                    }  in
                                                                    [uu____4287]
                                                                     in
                                                                    (uu____4284,
                                                                    [])  in
                                                                    ret
                                                                    uu____4275
                                                                    | 
                                                                    uu____4303
                                                                    ->
                                                                    let g_typ
                                                                    =
                                                                    let uu____4305
                                                                    =
                                                                    FStar_Options.__temp_fast_implicits
                                                                    ()  in
                                                                    if
                                                                    uu____4305
                                                                    then
                                                                    FStar_TypeChecker_TcTerm.check_type_of_well_typed_term
                                                                    false env
                                                                    term typ
                                                                    else
                                                                    (let term1
                                                                    =
                                                                    bnorm env
                                                                    term  in
                                                                    let uu____4308
                                                                    =
                                                                    let uu____4315
                                                                    =
                                                                    FStar_TypeChecker_Env.set_expected_typ
                                                                    env typ
                                                                     in
                                                                    env.FStar_TypeChecker_Env.type_of
                                                                    uu____4315
                                                                    term1  in
                                                                    match uu____4308
                                                                    with
                                                                    | 
                                                                    (uu____4316,uu____4317,g_typ)
                                                                    -> g_typ)
                                                                     in
                                                                    let uu____4319
                                                                    =
                                                                    goal_from_guard
                                                                    "apply_lemma solved arg"
                                                                    goal.FStar_Tactics_Types.context
                                                                    g_typ
                                                                    goal.FStar_Tactics_Types.opts
                                                                     in
                                                                    bind
                                                                    uu____4319
                                                                    (fun
                                                                    uu___60_4335
                                                                     ->
                                                                    match uu___60_4335
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
                                                            bind uu____4096
                                                              (fun goals_  ->
                                                                 let sub_goals
                                                                   =
                                                                   let uu____4403
                                                                    =
                                                                    FStar_List.map
                                                                    FStar_Pervasives_Native.fst
                                                                    goals_
                                                                     in
                                                                   FStar_List.flatten
                                                                    uu____4403
                                                                    in
                                                                 let smt_goals
                                                                   =
                                                                   let uu____4425
                                                                    =
                                                                    FStar_List.map
                                                                    FStar_Pervasives_Native.snd
                                                                    goals_
                                                                     in
                                                                   FStar_List.flatten
                                                                    uu____4425
                                                                    in
                                                                 let rec filter'
                                                                   a f xs =
                                                                   match xs
                                                                   with
                                                                   | 
                                                                   [] -> []
                                                                   | 
                                                                   x::xs1 ->
                                                                    let uu____4480
                                                                    = f x xs1
                                                                     in
                                                                    if
                                                                    uu____4480
                                                                    then
                                                                    let uu____4483
                                                                    =
                                                                    filter'
                                                                    () f xs1
                                                                     in x ::
                                                                    uu____4483
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
                                                                    let uu____4497
                                                                    =
                                                                    checkone
                                                                    g.FStar_Tactics_Types.witness
                                                                    goals  in
                                                                    Prims.op_Negation
                                                                    uu____4497))
                                                                    a438 a439)
                                                                    (Obj.magic
                                                                    sub_goals))
                                                                    in
                                                                 let uu____4498
                                                                   =
                                                                   proc_guard
                                                                    "apply_lemma guard"
                                                                    goal.FStar_Tactics_Types.context
                                                                    guard
                                                                    goal.FStar_Tactics_Types.opts
                                                                    in
                                                                 bind
                                                                   uu____4498
                                                                   (fun
                                                                    uu____4503
                                                                     ->
                                                                    let uu____4504
                                                                    =
                                                                    let uu____4507
                                                                    =
                                                                    let uu____4508
                                                                    =
                                                                    let uu____4509
                                                                    =
                                                                    FStar_Syntax_Util.mk_squash
                                                                    FStar_Syntax_Syntax.U_zero
                                                                    pre1  in
                                                                    istrivial
                                                                    goal.FStar_Tactics_Types.context
                                                                    uu____4509
                                                                     in
                                                                    Prims.op_Negation
                                                                    uu____4508
                                                                     in
                                                                    if
                                                                    uu____4507
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
                                                                    uu____4504
                                                                    (fun
                                                                    uu____4515
                                                                     ->
                                                                    let uu____4516
                                                                    =
                                                                    add_smt_goals
                                                                    smt_goals
                                                                     in
                                                                    bind
                                                                    uu____4516
                                                                    (fun
                                                                    uu____4520
                                                                     ->
                                                                    add_goals
                                                                    sub_goals1))))))))))))))
         in
      focus uu____3536  in
    FStar_All.pipe_left (wrap_err "apply_lemma") uu____3533
  
let (destruct_eq' :
  FStar_Reflection_Data.typ ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun typ  ->
    let uu____4540 = FStar_Syntax_Util.destruct_typ_as_formula typ  in
    match uu____4540 with
    | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn
        (l,uu____4550::(e1,uu____4552)::(e2,uu____4554)::[])) when
        FStar_Ident.lid_equals l FStar_Parser_Const.eq2_lid ->
        FStar_Pervasives_Native.Some (e1, e2)
    | uu____4613 -> FStar_Pervasives_Native.None
  
let (destruct_eq :
  FStar_Reflection_Data.typ ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun typ  ->
    let uu____4635 = destruct_eq' typ  in
    match uu____4635 with
    | FStar_Pervasives_Native.Some t -> FStar_Pervasives_Native.Some t
    | FStar_Pervasives_Native.None  ->
        let uu____4665 = FStar_Syntax_Util.un_squash typ  in
        (match uu____4665 with
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
        let uu____4721 = FStar_TypeChecker_Env.pop_bv e1  in
        match uu____4721 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (bv',e') ->
            if FStar_Syntax_Syntax.bv_eq bvar bv'
            then FStar_Pervasives_Native.Some (e', [])
            else
              (let uu____4769 = aux e'  in
               FStar_Util.map_opt uu____4769
                 (fun uu____4793  ->
                    match uu____4793 with | (e'',bvs) -> (e'', (bv' :: bvs))))
         in
      let uu____4814 = aux e  in
      FStar_Util.map_opt uu____4814
        (fun uu____4838  ->
           match uu____4838 with | (e',bvs) -> (e', (FStar_List.rev bvs)))
  
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
          let uu____4893 = split_env b1 g.FStar_Tactics_Types.context  in
          FStar_Util.map_opt uu____4893
            (fun uu____4917  ->
               match uu____4917 with
               | (e0,bvs) ->
                   let s1 bv =
                     let uu___97_4934 = bv  in
                     let uu____4935 =
                       FStar_Syntax_Subst.subst s bv.FStar_Syntax_Syntax.sort
                        in
                     {
                       FStar_Syntax_Syntax.ppname =
                         (uu___97_4934.FStar_Syntax_Syntax.ppname);
                       FStar_Syntax_Syntax.index =
                         (uu___97_4934.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort = uu____4935
                     }  in
                   let bvs1 = FStar_List.map s1 bvs  in
                   let c = push_bvs e0 (b2 :: bvs1)  in
                   let w =
                     FStar_Syntax_Subst.subst s g.FStar_Tactics_Types.witness
                      in
                   let t =
                     FStar_Syntax_Subst.subst s g.FStar_Tactics_Types.goal_ty
                      in
                   let uu___98_4944 = g  in
                   {
                     FStar_Tactics_Types.context = c;
                     FStar_Tactics_Types.witness = w;
                     FStar_Tactics_Types.goal_ty = t;
                     FStar_Tactics_Types.opts =
                       (uu___98_4944.FStar_Tactics_Types.opts);
                     FStar_Tactics_Types.is_guard =
                       (uu___98_4944.FStar_Tactics_Types.is_guard)
                   })
  
let (rewrite : FStar_Syntax_Syntax.binder -> Prims.unit tac) =
  fun h  ->
    bind cur_goal
      (fun goal  ->
         let uu____4957 = h  in
         match uu____4957 with
         | (bv,uu____4961) ->
             mlog
               (fun uu____4965  ->
                  let uu____4966 = FStar_Syntax_Print.bv_to_string bv  in
                  let uu____4967 =
                    tts goal.FStar_Tactics_Types.context
                      bv.FStar_Syntax_Syntax.sort
                     in
                  FStar_Util.print2 "+++Rewrite %s : %s\n" uu____4966
                    uu____4967)
               (fun uu____4970  ->
                  let uu____4971 =
                    split_env bv goal.FStar_Tactics_Types.context  in
                  match uu____4971 with
                  | FStar_Pervasives_Native.None  ->
                      fail "rewrite: binder not found in environment"
                  | FStar_Pervasives_Native.Some (e0,bvs) ->
                      let uu____5000 =
                        destruct_eq bv.FStar_Syntax_Syntax.sort  in
                      (match uu____5000 with
                       | FStar_Pervasives_Native.Some (x,e) ->
                           let uu____5015 =
                             let uu____5016 = FStar_Syntax_Subst.compress x
                                in
                             uu____5016.FStar_Syntax_Syntax.n  in
                           (match uu____5015 with
                            | FStar_Syntax_Syntax.Tm_name x1 ->
                                let s = [FStar_Syntax_Syntax.NT (x1, e)]  in
                                let s1 bv1 =
                                  let uu___99_5029 = bv1  in
                                  let uu____5030 =
                                    FStar_Syntax_Subst.subst s
                                      bv1.FStar_Syntax_Syntax.sort
                                     in
                                  {
                                    FStar_Syntax_Syntax.ppname =
                                      (uu___99_5029.FStar_Syntax_Syntax.ppname);
                                    FStar_Syntax_Syntax.index =
                                      (uu___99_5029.FStar_Syntax_Syntax.index);
                                    FStar_Syntax_Syntax.sort = uu____5030
                                  }  in
                                let bvs1 = FStar_List.map s1 bvs  in
                                let uu____5036 =
                                  let uu___100_5037 = goal  in
                                  let uu____5038 = push_bvs e0 (bv :: bvs1)
                                     in
                                  let uu____5039 =
                                    FStar_Syntax_Subst.subst s
                                      goal.FStar_Tactics_Types.witness
                                     in
                                  let uu____5040 =
                                    FStar_Syntax_Subst.subst s
                                      goal.FStar_Tactics_Types.goal_ty
                                     in
                                  {
                                    FStar_Tactics_Types.context = uu____5038;
                                    FStar_Tactics_Types.witness = uu____5039;
                                    FStar_Tactics_Types.goal_ty = uu____5040;
                                    FStar_Tactics_Types.opts =
                                      (uu___100_5037.FStar_Tactics_Types.opts);
                                    FStar_Tactics_Types.is_guard =
                                      (uu___100_5037.FStar_Tactics_Types.is_guard)
                                  }  in
                                replace_cur uu____5036
                            | uu____5041 ->
                                fail
                                  "rewrite: Not an equality hypothesis with a variable on the LHS")
                       | uu____5042 ->
                           fail "rewrite: Not an equality hypothesis")))
  
let (rename_to :
  FStar_Syntax_Syntax.binder -> Prims.string -> Prims.unit tac) =
  fun b  ->
    fun s  ->
      bind cur_goal
        (fun goal  ->
           let uu____5067 = b  in
           match uu____5067 with
           | (bv,uu____5071) ->
               let bv' =
                 FStar_Syntax_Syntax.freshen_bv
                   (let uu___101_5075 = bv  in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (FStar_Ident.mk_ident
                           (s,
                             ((bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange)));
                      FStar_Syntax_Syntax.index =
                        (uu___101_5075.FStar_Syntax_Syntax.index);
                      FStar_Syntax_Syntax.sort =
                        (uu___101_5075.FStar_Syntax_Syntax.sort)
                    })
                  in
               let s1 =
                 let uu____5079 =
                   let uu____5080 =
                     let uu____5087 = FStar_Syntax_Syntax.bv_to_name bv'  in
                     (bv, uu____5087)  in
                   FStar_Syntax_Syntax.NT uu____5080  in
                 [uu____5079]  in
               let uu____5088 = subst_goal bv bv' s1 goal  in
               (match uu____5088 with
                | FStar_Pervasives_Native.None  ->
                    fail "rename_to: binder not found in environment"
                | FStar_Pervasives_Native.Some goal1 -> replace_cur goal1))
  
let (binder_retype : FStar_Syntax_Syntax.binder -> Prims.unit tac) =
  fun b  ->
    bind cur_goal
      (fun goal  ->
         let uu____5107 = b  in
         match uu____5107 with
         | (bv,uu____5111) ->
             let uu____5112 = split_env bv goal.FStar_Tactics_Types.context
                in
             (match uu____5112 with
              | FStar_Pervasives_Native.None  ->
                  fail "binder_retype: binder is not present in environment"
              | FStar_Pervasives_Native.Some (e0,bvs) ->
                  let uu____5141 = FStar_Syntax_Util.type_u ()  in
                  (match uu____5141 with
                   | (ty,u) ->
                       let uu____5150 = new_uvar "binder_retype" e0 ty  in
                       bind uu____5150
                         (fun t'  ->
                            let bv'' =
                              let uu___102_5160 = bv  in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___102_5160.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___102_5160.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = t'
                              }  in
                            let s =
                              let uu____5164 =
                                let uu____5165 =
                                  let uu____5172 =
                                    FStar_Syntax_Syntax.bv_to_name bv''  in
                                  (bv, uu____5172)  in
                                FStar_Syntax_Syntax.NT uu____5165  in
                              [uu____5164]  in
                            let bvs1 =
                              FStar_List.map
                                (fun b1  ->
                                   let uu___103_5180 = b1  in
                                   let uu____5181 =
                                     FStar_Syntax_Subst.subst s
                                       b1.FStar_Syntax_Syntax.sort
                                      in
                                   {
                                     FStar_Syntax_Syntax.ppname =
                                       (uu___103_5180.FStar_Syntax_Syntax.ppname);
                                     FStar_Syntax_Syntax.index =
                                       (uu___103_5180.FStar_Syntax_Syntax.index);
                                     FStar_Syntax_Syntax.sort = uu____5181
                                   }) bvs
                               in
                            let env' = push_bvs e0 (bv'' :: bvs1)  in
                            bind __dismiss
                              (fun uu____5187  ->
                                 let uu____5188 =
                                   let uu____5191 =
                                     let uu____5194 =
                                       let uu___104_5195 = goal  in
                                       let uu____5196 =
                                         FStar_Syntax_Subst.subst s
                                           goal.FStar_Tactics_Types.witness
                                          in
                                       let uu____5197 =
                                         FStar_Syntax_Subst.subst s
                                           goal.FStar_Tactics_Types.goal_ty
                                          in
                                       {
                                         FStar_Tactics_Types.context = env';
                                         FStar_Tactics_Types.witness =
                                           uu____5196;
                                         FStar_Tactics_Types.goal_ty =
                                           uu____5197;
                                         FStar_Tactics_Types.opts =
                                           (uu___104_5195.FStar_Tactics_Types.opts);
                                         FStar_Tactics_Types.is_guard =
                                           (uu___104_5195.FStar_Tactics_Types.is_guard)
                                       }  in
                                     [uu____5194]  in
                                   add_goals uu____5191  in
                                 bind uu____5188
                                   (fun uu____5200  ->
                                      let uu____5201 =
                                        FStar_Syntax_Util.mk_eq2
                                          (FStar_Syntax_Syntax.U_succ u) ty
                                          bv.FStar_Syntax_Syntax.sort t'
                                         in
                                      add_irrelevant_goal
                                        "binder_retype equation" e0
                                        uu____5201
                                        goal.FStar_Tactics_Types.opts))))))
  
let (norm_binder_type :
  FStar_Syntax_Embeddings.norm_step Prims.list ->
    FStar_Syntax_Syntax.binder -> Prims.unit tac)
  =
  fun s  ->
    fun b  ->
      bind cur_goal
        (fun goal  ->
           let uu____5222 = b  in
           match uu____5222 with
           | (bv,uu____5226) ->
               let uu____5227 = split_env bv goal.FStar_Tactics_Types.context
                  in
               (match uu____5227 with
                | FStar_Pervasives_Native.None  ->
                    fail
                      "binder_retype: binder is not present in environment"
                | FStar_Pervasives_Native.Some (e0,bvs) ->
                    let steps =
                      let uu____5259 =
                        FStar_TypeChecker_Normalize.tr_norm_steps s  in
                      FStar_List.append
                        [FStar_TypeChecker_Normalize.Reify;
                        FStar_TypeChecker_Normalize.UnfoldTac] uu____5259
                       in
                    let sort' =
                      normalize steps e0 bv.FStar_Syntax_Syntax.sort  in
                    let bv' =
                      let uu___105_5264 = bv  in
                      {
                        FStar_Syntax_Syntax.ppname =
                          (uu___105_5264.FStar_Syntax_Syntax.ppname);
                        FStar_Syntax_Syntax.index =
                          (uu___105_5264.FStar_Syntax_Syntax.index);
                        FStar_Syntax_Syntax.sort = sort'
                      }  in
                    let env' = push_bvs e0 (bv' :: bvs)  in
                    replace_cur
                      (let uu___106_5268 = goal  in
                       {
                         FStar_Tactics_Types.context = env';
                         FStar_Tactics_Types.witness =
                           (uu___106_5268.FStar_Tactics_Types.witness);
                         FStar_Tactics_Types.goal_ty =
                           (uu___106_5268.FStar_Tactics_Types.goal_ty);
                         FStar_Tactics_Types.opts =
                           (uu___106_5268.FStar_Tactics_Types.opts);
                         FStar_Tactics_Types.is_guard =
                           (uu___106_5268.FStar_Tactics_Types.is_guard)
                       })))
  
let (revert : Prims.unit tac) =
  bind cur_goal
    (fun goal  ->
       let uu____5276 =
         FStar_TypeChecker_Env.pop_bv goal.FStar_Tactics_Types.context  in
       match uu____5276 with
       | FStar_Pervasives_Native.None  -> fail "Cannot revert; empty context"
       | FStar_Pervasives_Native.Some (x,env') ->
           let typ' =
             let uu____5298 =
               FStar_Syntax_Syntax.mk_Total goal.FStar_Tactics_Types.goal_ty
                in
             FStar_Syntax_Util.arrow [(x, FStar_Pervasives_Native.None)]
               uu____5298
              in
           let w' =
             FStar_Syntax_Util.abs [(x, FStar_Pervasives_Native.None)]
               goal.FStar_Tactics_Types.witness FStar_Pervasives_Native.None
              in
           replace_cur
             (let uu___107_5332 = goal  in
              {
                FStar_Tactics_Types.context = env';
                FStar_Tactics_Types.witness = w';
                FStar_Tactics_Types.goal_ty = typ';
                FStar_Tactics_Types.opts =
                  (uu___107_5332.FStar_Tactics_Types.opts);
                FStar_Tactics_Types.is_guard =
                  (uu___107_5332.FStar_Tactics_Types.is_guard)
              }))
  
let (free_in :
  FStar_Syntax_Syntax.bv -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun bv  ->
    fun t  ->
      let uu____5339 = FStar_Syntax_Free.names t  in
      FStar_Util.set_mem bv uu____5339
  
let rec (clear : FStar_Syntax_Syntax.binder -> Prims.unit tac) =
  fun b  ->
    let bv = FStar_Pervasives_Native.fst b  in
    bind cur_goal
      (fun goal  ->
         mlog
           (fun uu____5355  ->
              let uu____5356 = FStar_Syntax_Print.binder_to_string b  in
              let uu____5357 =
                let uu____5358 =
                  let uu____5359 =
                    FStar_TypeChecker_Env.all_binders
                      goal.FStar_Tactics_Types.context
                     in
                  FStar_All.pipe_right uu____5359 FStar_List.length  in
                FStar_All.pipe_right uu____5358 FStar_Util.string_of_int  in
              FStar_Util.print2 "Clear of (%s), env has %s binders\n"
                uu____5356 uu____5357)
           (fun uu____5370  ->
              let uu____5371 = split_env bv goal.FStar_Tactics_Types.context
                 in
              match uu____5371 with
              | FStar_Pervasives_Native.None  ->
                  fail "Cannot clear; binder not in environment"
              | FStar_Pervasives_Native.Some (e',bvs) ->
                  let rec check1 bvs1 =
                    match bvs1 with
                    | [] -> ret ()
                    | bv'::bvs2 ->
                        let uu____5416 =
                          free_in bv bv'.FStar_Syntax_Syntax.sort  in
                        if uu____5416
                        then
                          let uu____5419 =
                            let uu____5420 =
                              FStar_Syntax_Print.bv_to_string bv'  in
                            FStar_Util.format1
                              "Cannot clear; binder present in the type of %s"
                              uu____5420
                             in
                          fail uu____5419
                        else check1 bvs2
                     in
                  let uu____5422 =
                    free_in bv goal.FStar_Tactics_Types.goal_ty  in
                  if uu____5422
                  then fail "Cannot clear; binder present in goal"
                  else
                    (let uu____5426 = check1 bvs  in
                     bind uu____5426
                       (fun uu____5432  ->
                          let env' = push_bvs e' bvs  in
                          let uu____5434 =
                            new_uvar "clear.witness" env'
                              goal.FStar_Tactics_Types.goal_ty
                             in
                          bind uu____5434
                            (fun ut  ->
                               let uu____5440 =
                                 do_unify goal.FStar_Tactics_Types.context
                                   goal.FStar_Tactics_Types.witness ut
                                  in
                               bind uu____5440
                                 (fun b1  ->
                                    if b1
                                    then
                                      replace_cur
                                        (let uu___108_5449 = goal  in
                                         {
                                           FStar_Tactics_Types.context = env';
                                           FStar_Tactics_Types.witness = ut;
                                           FStar_Tactics_Types.goal_ty =
                                             (uu___108_5449.FStar_Tactics_Types.goal_ty);
                                           FStar_Tactics_Types.opts =
                                             (uu___108_5449.FStar_Tactics_Types.opts);
                                           FStar_Tactics_Types.is_guard =
                                             (uu___108_5449.FStar_Tactics_Types.is_guard)
                                         })
                                    else
                                      fail
                                        "Cannot clear; binder appears in witness"))))))
  
let (clear_top : Prims.unit tac) =
  bind cur_goal
    (fun goal  ->
       let uu____5458 =
         FStar_TypeChecker_Env.pop_bv goal.FStar_Tactics_Types.context  in
       match uu____5458 with
       | FStar_Pervasives_Native.None  -> fail "Cannot clear; empty context"
       | FStar_Pervasives_Native.Some (x,uu____5472) ->
           let uu____5477 = FStar_Syntax_Syntax.mk_binder x  in
           clear uu____5477)
  
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
           let uu___109_5493 = g  in
           {
             FStar_Tactics_Types.context = ctx';
             FStar_Tactics_Types.witness =
               (uu___109_5493.FStar_Tactics_Types.witness);
             FStar_Tactics_Types.goal_ty =
               (uu___109_5493.FStar_Tactics_Types.goal_ty);
             FStar_Tactics_Types.opts =
               (uu___109_5493.FStar_Tactics_Types.opts);
             FStar_Tactics_Types.is_guard =
               (uu___109_5493.FStar_Tactics_Types.is_guard)
           }  in
         bind __dismiss (fun uu____5495  -> add_goals [g']))
  
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
           let uu___110_5511 = g  in
           {
             FStar_Tactics_Types.context = ctx';
             FStar_Tactics_Types.witness =
               (uu___110_5511.FStar_Tactics_Types.witness);
             FStar_Tactics_Types.goal_ty =
               (uu___110_5511.FStar_Tactics_Types.goal_ty);
             FStar_Tactics_Types.opts =
               (uu___110_5511.FStar_Tactics_Types.opts);
             FStar_Tactics_Types.is_guard =
               (uu___110_5511.FStar_Tactics_Types.is_guard)
           }  in
         bind __dismiss (fun uu____5513  -> add_goals [g']))
  
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
            let uu____5545 = FStar_Syntax_Subst.compress t  in
            uu____5545.FStar_Syntax_Syntax.n  in
          let uu____5548 =
            if d = FStar_Tactics_Types.TopDown
            then
              f env
                (let uu___114_5554 = t  in
                 {
                   FStar_Syntax_Syntax.n = tn;
                   FStar_Syntax_Syntax.pos =
                     (uu___114_5554.FStar_Syntax_Syntax.pos);
                   FStar_Syntax_Syntax.vars =
                     (uu___114_5554.FStar_Syntax_Syntax.vars)
                 })
            else ret t  in
          bind uu____5548
            (fun t1  ->
               let ff = tac_fold_env d f env  in
               let tn1 =
                 let uu____5568 =
                   let uu____5569 = FStar_Syntax_Subst.compress t1  in
                   uu____5569.FStar_Syntax_Syntax.n  in
                 match uu____5568 with
                 | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
                     let uu____5596 = ff hd1  in
                     bind uu____5596
                       (fun hd2  ->
                          let fa uu____5616 =
                            match uu____5616 with
                            | (a,q) ->
                                let uu____5629 = ff a  in
                                bind uu____5629 (fun a1  -> ret (a1, q))
                             in
                          let uu____5642 = mapM fa args  in
                          bind uu____5642
                            (fun args1  ->
                               ret (FStar_Syntax_Syntax.Tm_app (hd2, args1))))
                 | FStar_Syntax_Syntax.Tm_abs (bs,t2,k) ->
                     let uu____5702 = FStar_Syntax_Subst.open_term bs t2  in
                     (match uu____5702 with
                      | (bs1,t') ->
                          let uu____5711 =
                            let uu____5714 =
                              FStar_TypeChecker_Env.push_binders env bs1  in
                            tac_fold_env d f uu____5714 t'  in
                          bind uu____5711
                            (fun t''  ->
                               let uu____5718 =
                                 let uu____5719 =
                                   let uu____5736 =
                                     FStar_Syntax_Subst.close_binders bs1  in
                                   let uu____5737 =
                                     FStar_Syntax_Subst.close bs1 t''  in
                                   (uu____5736, uu____5737, k)  in
                                 FStar_Syntax_Syntax.Tm_abs uu____5719  in
                               ret uu____5718))
                 | FStar_Syntax_Syntax.Tm_arrow (bs,k) -> ret tn
                 | FStar_Syntax_Syntax.Tm_match (hd1,brs) ->
                     let uu____5796 = ff hd1  in
                     bind uu____5796
                       (fun hd2  ->
                          let ffb br =
                            let uu____5809 =
                              FStar_Syntax_Subst.open_branch br  in
                            match uu____5809 with
                            | (pat,w,e) ->
                                let uu____5831 = ff e  in
                                bind uu____5831
                                  (fun e1  ->
                                     let br1 =
                                       FStar_Syntax_Subst.close_branch
                                         (pat, w, e1)
                                        in
                                     ret br1)
                             in
                          let uu____5844 = mapM ffb brs  in
                          bind uu____5844
                            (fun brs1  ->
                               ret (FStar_Syntax_Syntax.Tm_match (hd2, brs1))))
                 | FStar_Syntax_Syntax.Tm_let
                     ((false
                       ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl bv;
                          FStar_Syntax_Syntax.lbunivs = uu____5858;
                          FStar_Syntax_Syntax.lbtyp = uu____5859;
                          FStar_Syntax_Syntax.lbeff = uu____5860;
                          FStar_Syntax_Syntax.lbdef = def;
                          FStar_Syntax_Syntax.lbattrs = uu____5862;
                          FStar_Syntax_Syntax.lbpos = uu____5863;_}::[]),e)
                     ->
                     let lb =
                       let uu____5888 =
                         let uu____5889 = FStar_Syntax_Subst.compress t1  in
                         uu____5889.FStar_Syntax_Syntax.n  in
                       match uu____5888 with
                       | FStar_Syntax_Syntax.Tm_let
                           ((false ,lb::[]),uu____5893) -> lb
                       | uu____5906 -> failwith "impossible"  in
                     let fflb lb1 =
                       let uu____5913 = ff lb1.FStar_Syntax_Syntax.lbdef  in
                       bind uu____5913
                         (fun def1  ->
                            ret
                              (let uu___111_5919 = lb1  in
                               {
                                 FStar_Syntax_Syntax.lbname =
                                   (uu___111_5919.FStar_Syntax_Syntax.lbname);
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___111_5919.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp =
                                   (uu___111_5919.FStar_Syntax_Syntax.lbtyp);
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___111_5919.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def1;
                                 FStar_Syntax_Syntax.lbattrs =
                                   (uu___111_5919.FStar_Syntax_Syntax.lbattrs);
                                 FStar_Syntax_Syntax.lbpos =
                                   (uu___111_5919.FStar_Syntax_Syntax.lbpos)
                               }))
                        in
                     let uu____5920 = fflb lb  in
                     bind uu____5920
                       (fun lb1  ->
                          let uu____5929 =
                            let uu____5934 =
                              let uu____5935 =
                                FStar_Syntax_Syntax.mk_binder bv  in
                              [uu____5935]  in
                            FStar_Syntax_Subst.open_term uu____5934 e  in
                          match uu____5929 with
                          | (bs,e1) ->
                              let uu____5940 = ff e1  in
                              bind uu____5940
                                (fun e2  ->
                                   let e3 = FStar_Syntax_Subst.close bs e2
                                      in
                                   ret
                                     (FStar_Syntax_Syntax.Tm_let
                                        ((false, [lb1]), e3))))
                 | FStar_Syntax_Syntax.Tm_let ((true ,lbs),e) ->
                     let fflb lb =
                       let uu____5977 = ff lb.FStar_Syntax_Syntax.lbdef  in
                       bind uu____5977
                         (fun def  ->
                            ret
                              (let uu___112_5983 = lb  in
                               {
                                 FStar_Syntax_Syntax.lbname =
                                   (uu___112_5983.FStar_Syntax_Syntax.lbname);
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___112_5983.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp =
                                   (uu___112_5983.FStar_Syntax_Syntax.lbtyp);
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___112_5983.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def;
                                 FStar_Syntax_Syntax.lbattrs =
                                   (uu___112_5983.FStar_Syntax_Syntax.lbattrs);
                                 FStar_Syntax_Syntax.lbpos =
                                   (uu___112_5983.FStar_Syntax_Syntax.lbpos)
                               }))
                        in
                     let uu____5984 = FStar_Syntax_Subst.open_let_rec lbs e
                        in
                     (match uu____5984 with
                      | (lbs1,e1) ->
                          let uu____5999 = mapM fflb lbs1  in
                          bind uu____5999
                            (fun lbs2  ->
                               let uu____6011 = ff e1  in
                               bind uu____6011
                                 (fun e2  ->
                                    let uu____6019 =
                                      FStar_Syntax_Subst.close_let_rec lbs2
                                        e2
                                       in
                                    match uu____6019 with
                                    | (lbs3,e3) ->
                                        ret
                                          (FStar_Syntax_Syntax.Tm_let
                                             ((true, lbs3), e3)))))
                 | FStar_Syntax_Syntax.Tm_ascribed (t2,asc,eff) ->
                     let uu____6085 = ff t2  in
                     bind uu____6085
                       (fun t3  ->
                          ret
                            (FStar_Syntax_Syntax.Tm_ascribed (t3, asc, eff)))
                 | FStar_Syntax_Syntax.Tm_meta (t2,m) ->
                     let uu____6114 = ff t2  in
                     bind uu____6114
                       (fun t3  -> ret (FStar_Syntax_Syntax.Tm_meta (t3, m)))
                 | uu____6119 -> ret tn  in
               bind tn1
                 (fun tn2  ->
                    let t' =
                      let uu___113_6126 = t1  in
                      {
                        FStar_Syntax_Syntax.n = tn2;
                        FStar_Syntax_Syntax.pos =
                          (uu___113_6126.FStar_Syntax_Syntax.pos);
                        FStar_Syntax_Syntax.vars =
                          (uu___113_6126.FStar_Syntax_Syntax.vars)
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
            let uu____6155 = FStar_TypeChecker_TcTerm.tc_term env t  in
            match uu____6155 with
            | (t1,lcomp,g) ->
                let uu____6167 =
                  (let uu____6170 =
                     FStar_Syntax_Util.is_pure_or_ghost_lcomp lcomp  in
                   Prims.op_Negation uu____6170) ||
                    (let uu____6172 = FStar_TypeChecker_Rel.is_trivial g  in
                     Prims.op_Negation uu____6172)
                   in
                if uu____6167
                then ret t1
                else
                  (let rewrite_eq =
                     let typ = lcomp.FStar_Syntax_Syntax.res_typ  in
                     let uu____6182 = new_uvar "pointwise_rec" env typ  in
                     bind uu____6182
                       (fun ut  ->
                          log ps
                            (fun uu____6193  ->
                               let uu____6194 =
                                 FStar_Syntax_Print.term_to_string t1  in
                               let uu____6195 =
                                 FStar_Syntax_Print.term_to_string ut  in
                               FStar_Util.print2
                                 "Pointwise_rec: making equality\n\t%s ==\n\t%s\n"
                                 uu____6194 uu____6195);
                          (let uu____6196 =
                             let uu____6199 =
                               let uu____6200 =
                                 FStar_TypeChecker_TcTerm.universe_of env typ
                                  in
                               FStar_Syntax_Util.mk_eq2 uu____6200 typ t1 ut
                                in
                             add_irrelevant_goal "pointwise_rec equation" env
                               uu____6199 opts
                              in
                           bind uu____6196
                             (fun uu____6203  ->
                                let uu____6204 =
                                  bind tau
                                    (fun uu____6210  ->
                                       let ut1 =
                                         FStar_TypeChecker_Normalize.reduce_uvar_solutions
                                           env ut
                                          in
                                       log ps
                                         (fun uu____6216  ->
                                            let uu____6217 =
                                              FStar_Syntax_Print.term_to_string
                                                t1
                                               in
                                            let uu____6218 =
                                              FStar_Syntax_Print.term_to_string
                                                ut1
                                               in
                                            FStar_Util.print2
                                              "Pointwise_rec: succeeded rewriting\n\t%s to\n\t%s\n"
                                              uu____6217 uu____6218);
                                       ret ut1)
                                   in
                                focus uu____6204)))
                      in
                   let uu____6219 = trytac' rewrite_eq  in
                   bind uu____6219
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
          let uu____6367 = FStar_Syntax_Subst.compress t  in
          maybe_continue ctrl uu____6367
            (fun t1  ->
               let uu____6371 =
                 f env
                   (let uu___117_6380 = t1  in
                    {
                      FStar_Syntax_Syntax.n = (t1.FStar_Syntax_Syntax.n);
                      FStar_Syntax_Syntax.pos =
                        (uu___117_6380.FStar_Syntax_Syntax.pos);
                      FStar_Syntax_Syntax.vars =
                        (uu___117_6380.FStar_Syntax_Syntax.vars)
                    })
                  in
               bind uu____6371
                 (fun uu____6392  ->
                    match uu____6392 with
                    | (t2,ctrl1) ->
                        maybe_continue ctrl1 t2
                          (fun t3  ->
                             let uu____6411 =
                               let uu____6412 =
                                 FStar_Syntax_Subst.compress t3  in
                               uu____6412.FStar_Syntax_Syntax.n  in
                             match uu____6411 with
                             | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
                                 let uu____6445 =
                                   ctrl_tac_fold f env ctrl1 hd1  in
                                 bind uu____6445
                                   (fun uu____6470  ->
                                      match uu____6470 with
                                      | (hd2,ctrl2) ->
                                          let ctrl3 = keep_going ctrl2  in
                                          let uu____6486 =
                                            ctrl_tac_fold_args f env ctrl3
                                              args
                                             in
                                          bind uu____6486
                                            (fun uu____6513  ->
                                               match uu____6513 with
                                               | (args1,ctrl4) ->
                                                   ret
                                                     ((let uu___115_6543 = t3
                                                          in
                                                       {
                                                         FStar_Syntax_Syntax.n
                                                           =
                                                           (FStar_Syntax_Syntax.Tm_app
                                                              (hd2, args1));
                                                         FStar_Syntax_Syntax.pos
                                                           =
                                                           (uu___115_6543.FStar_Syntax_Syntax.pos);
                                                         FStar_Syntax_Syntax.vars
                                                           =
                                                           (uu___115_6543.FStar_Syntax_Syntax.vars)
                                                       }), ctrl4)))
                             | FStar_Syntax_Syntax.Tm_abs (bs,t4,k) ->
                                 let uu____6569 =
                                   FStar_Syntax_Subst.open_term bs t4  in
                                 (match uu____6569 with
                                  | (bs1,t') ->
                                      let uu____6584 =
                                        let uu____6591 =
                                          FStar_TypeChecker_Env.push_binders
                                            env bs1
                                           in
                                        ctrl_tac_fold f uu____6591 ctrl1 t'
                                         in
                                      bind uu____6584
                                        (fun uu____6609  ->
                                           match uu____6609 with
                                           | (t'',ctrl2) ->
                                               let uu____6624 =
                                                 let uu____6631 =
                                                   let uu___116_6634 = t4  in
                                                   let uu____6637 =
                                                     let uu____6638 =
                                                       let uu____6655 =
                                                         FStar_Syntax_Subst.close_binders
                                                           bs1
                                                          in
                                                       let uu____6656 =
                                                         FStar_Syntax_Subst.close
                                                           bs1 t''
                                                          in
                                                       (uu____6655,
                                                         uu____6656, k)
                                                        in
                                                     FStar_Syntax_Syntax.Tm_abs
                                                       uu____6638
                                                      in
                                                   {
                                                     FStar_Syntax_Syntax.n =
                                                       uu____6637;
                                                     FStar_Syntax_Syntax.pos
                                                       =
                                                       (uu___116_6634.FStar_Syntax_Syntax.pos);
                                                     FStar_Syntax_Syntax.vars
                                                       =
                                                       (uu___116_6634.FStar_Syntax_Syntax.vars)
                                                   }  in
                                                 (uu____6631, ctrl2)  in
                                               ret uu____6624))
                             | FStar_Syntax_Syntax.Tm_arrow (bs,k) ->
                                 ret (t3, ctrl1)
                             | uu____6689 -> ret (t3, ctrl1))))

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
              let uu____6740 = ctrl_tac_fold f env ctrl t  in
              bind uu____6740
                (fun uu____6768  ->
                   match uu____6768 with
                   | (t1,ctrl1) ->
                       let uu____6787 = ctrl_tac_fold_args f env ctrl1 ts1
                          in
                       bind uu____6787
                         (fun uu____6818  ->
                            match uu____6818 with
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
              let uu____6902 =
                let uu____6909 =
                  add_irrelevant_goal "dummy" env FStar_Syntax_Util.t_true
                    opts
                   in
                bind uu____6909
                  (fun uu____6918  ->
                     let uu____6919 = ctrl t1  in
                     bind uu____6919
                       (fun res  -> bind trivial (fun uu____6946  -> ret res)))
                 in
              bind uu____6902
                (fun uu____6962  ->
                   match uu____6962 with
                   | (should_rewrite,ctrl1) ->
                       if Prims.op_Negation should_rewrite
                       then ret (t1, ctrl1)
                       else
                         (let uu____6986 =
                            FStar_TypeChecker_TcTerm.tc_term env t1  in
                          match uu____6986 with
                          | (t2,lcomp,g) ->
                              let uu____7002 =
                                (let uu____7005 =
                                   FStar_Syntax_Util.is_pure_or_ghost_lcomp
                                     lcomp
                                    in
                                 Prims.op_Negation uu____7005) ||
                                  (let uu____7007 =
                                     FStar_TypeChecker_Rel.is_trivial g  in
                                   Prims.op_Negation uu____7007)
                                 in
                              if uu____7002
                              then ret (t2, globalStop)
                              else
                                (let typ = lcomp.FStar_Syntax_Syntax.res_typ
                                    in
                                 let uu____7022 =
                                   new_uvar "pointwise_rec" env typ  in
                                 bind uu____7022
                                   (fun ut  ->
                                      log ps
                                        (fun uu____7037  ->
                                           let uu____7038 =
                                             FStar_Syntax_Print.term_to_string
                                               t2
                                              in
                                           let uu____7039 =
                                             FStar_Syntax_Print.term_to_string
                                               ut
                                              in
                                           FStar_Util.print2
                                             "Pointwise_rec: making equality\n\t%s ==\n\t%s\n"
                                             uu____7038 uu____7039);
                                      (let uu____7040 =
                                         let uu____7043 =
                                           let uu____7044 =
                                             FStar_TypeChecker_TcTerm.universe_of
                                               env typ
                                              in
                                           FStar_Syntax_Util.mk_eq2
                                             uu____7044 typ t2 ut
                                            in
                                         add_irrelevant_goal
                                           "rewrite_rec equation" env
                                           uu____7043 opts
                                          in
                                       bind uu____7040
                                         (fun uu____7051  ->
                                            let uu____7052 =
                                              bind rewriter
                                                (fun uu____7066  ->
                                                   let ut1 =
                                                     FStar_TypeChecker_Normalize.reduce_uvar_solutions
                                                       env ut
                                                      in
                                                   log ps
                                                     (fun uu____7072  ->
                                                        let uu____7073 =
                                                          FStar_Syntax_Print.term_to_string
                                                            t2
                                                           in
                                                        let uu____7074 =
                                                          FStar_Syntax_Print.term_to_string
                                                            ut1
                                                           in
                                                        FStar_Util.print2
                                                          "rewrite_rec: succeeded rewriting\n\t%s to\n\t%s\n"
                                                          uu____7073
                                                          uu____7074);
                                                   ret (ut1, ctrl1))
                                               in
                                            focus uu____7052))))))
  
let (topdown_rewrite :
  (FStar_Syntax_Syntax.term ->
     (Prims.bool,FStar_BigInt.t) FStar_Pervasives_Native.tuple2 tac)
    -> Prims.unit tac -> Prims.unit tac)
  =
  fun ctrl  ->
    fun rewriter  ->
      bind get
        (fun ps  ->
           let uu____7118 =
             match ps.FStar_Tactics_Types.goals with
             | g::gs -> (g, gs)
             | [] -> failwith "Pointwise: no goals"  in
           match uu____7118 with
           | (g,gs) ->
               let gt1 = g.FStar_Tactics_Types.goal_ty  in
               (log ps
                  (fun uu____7155  ->
                     let uu____7156 = FStar_Syntax_Print.term_to_string gt1
                        in
                     FStar_Util.print1 "Pointwise starting with %s\n"
                       uu____7156);
                bind dismiss_all
                  (fun uu____7159  ->
                     let uu____7160 =
                       ctrl_tac_fold
                         (rewrite_rec ps ctrl rewriter
                            g.FStar_Tactics_Types.opts)
                         g.FStar_Tactics_Types.context keepGoing gt1
                        in
                     bind uu____7160
                       (fun uu____7178  ->
                          match uu____7178 with
                          | (gt',uu____7186) ->
                              (log ps
                                 (fun uu____7190  ->
                                    let uu____7191 =
                                      FStar_Syntax_Print.term_to_string gt'
                                       in
                                    FStar_Util.print1
                                      "Pointwise seems to have succeded with %s\n"
                                      uu____7191);
                               (let uu____7192 = push_goals gs  in
                                bind uu____7192
                                  (fun uu____7196  ->
                                     add_goals
                                       [(let uu___118_7198 = g  in
                                         {
                                           FStar_Tactics_Types.context =
                                             (uu___118_7198.FStar_Tactics_Types.context);
                                           FStar_Tactics_Types.witness =
                                             (uu___118_7198.FStar_Tactics_Types.witness);
                                           FStar_Tactics_Types.goal_ty = gt';
                                           FStar_Tactics_Types.opts =
                                             (uu___118_7198.FStar_Tactics_Types.opts);
                                           FStar_Tactics_Types.is_guard =
                                             (uu___118_7198.FStar_Tactics_Types.is_guard)
                                         })])))))))
  
let (pointwise :
  FStar_Tactics_Types.direction -> Prims.unit tac -> Prims.unit tac) =
  fun d  ->
    fun tau  ->
      bind get
        (fun ps  ->
           let uu____7220 =
             match ps.FStar_Tactics_Types.goals with
             | g::gs -> (g, gs)
             | [] -> failwith "Pointwise: no goals"  in
           match uu____7220 with
           | (g,gs) ->
               let gt1 = g.FStar_Tactics_Types.goal_ty  in
               (log ps
                  (fun uu____7257  ->
                     let uu____7258 = FStar_Syntax_Print.term_to_string gt1
                        in
                     FStar_Util.print1 "Pointwise starting with %s\n"
                       uu____7258);
                bind dismiss_all
                  (fun uu____7261  ->
                     let uu____7262 =
                       tac_fold_env d
                         (pointwise_rec ps tau g.FStar_Tactics_Types.opts)
                         g.FStar_Tactics_Types.context gt1
                        in
                     bind uu____7262
                       (fun gt'  ->
                          log ps
                            (fun uu____7272  ->
                               let uu____7273 =
                                 FStar_Syntax_Print.term_to_string gt'  in
                               FStar_Util.print1
                                 "Pointwise seems to have succeded with %s\n"
                                 uu____7273);
                          (let uu____7274 = push_goals gs  in
                           bind uu____7274
                             (fun uu____7278  ->
                                add_goals
                                  [(let uu___119_7280 = g  in
                                    {
                                      FStar_Tactics_Types.context =
                                        (uu___119_7280.FStar_Tactics_Types.context);
                                      FStar_Tactics_Types.witness =
                                        (uu___119_7280.FStar_Tactics_Types.witness);
                                      FStar_Tactics_Types.goal_ty = gt';
                                      FStar_Tactics_Types.opts =
                                        (uu___119_7280.FStar_Tactics_Types.opts);
                                      FStar_Tactics_Types.is_guard =
                                        (uu___119_7280.FStar_Tactics_Types.is_guard)
                                    })]))))))
  
let (trefl : Prims.unit tac) =
  bind cur_goal
    (fun g  ->
       let uu____7300 =
         FStar_Syntax_Util.un_squash g.FStar_Tactics_Types.goal_ty  in
       match uu____7300 with
       | FStar_Pervasives_Native.Some t ->
           let uu____7312 = FStar_Syntax_Util.head_and_args' t  in
           (match uu____7312 with
            | (hd1,args) ->
                let uu____7345 =
                  let uu____7358 =
                    let uu____7359 = FStar_Syntax_Util.un_uinst hd1  in
                    uu____7359.FStar_Syntax_Syntax.n  in
                  (uu____7358, args)  in
                (match uu____7345 with
                 | (FStar_Syntax_Syntax.Tm_fvar
                    fv,uu____7373::(l,uu____7375)::(r,uu____7377)::[]) when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.eq2_lid
                     ->
                     let uu____7424 =
                       do_unify g.FStar_Tactics_Types.context l r  in
                     bind uu____7424
                       (fun b  ->
                          if Prims.op_Negation b
                          then
                            let uu____7433 =
                              tts g.FStar_Tactics_Types.context l  in
                            let uu____7434 =
                              tts g.FStar_Tactics_Types.context r  in
                            fail2 "trefl: not a trivial equality (%s vs %s)"
                              uu____7433 uu____7434
                          else solve g FStar_Syntax_Util.exp_unit)
                 | (hd2,uu____7437) ->
                     let uu____7454 = tts g.FStar_Tactics_Types.context t  in
                     fail1 "trefl: not an equality (%s)" uu____7454))
       | FStar_Pervasives_Native.None  -> fail "not an irrelevant goal")
  
let (dup : Prims.unit tac) =
  bind cur_goal
    (fun g  ->
       let uu____7464 =
         new_uvar "dup" g.FStar_Tactics_Types.context
           g.FStar_Tactics_Types.goal_ty
          in
       bind uu____7464
         (fun u  ->
            let g' =
              let uu___120_7471 = g  in
              {
                FStar_Tactics_Types.context =
                  (uu___120_7471.FStar_Tactics_Types.context);
                FStar_Tactics_Types.witness = u;
                FStar_Tactics_Types.goal_ty =
                  (uu___120_7471.FStar_Tactics_Types.goal_ty);
                FStar_Tactics_Types.opts =
                  (uu___120_7471.FStar_Tactics_Types.opts);
                FStar_Tactics_Types.is_guard =
                  (uu___120_7471.FStar_Tactics_Types.is_guard)
              }  in
            bind __dismiss
              (fun uu____7474  ->
                 let uu____7475 =
                   let uu____7478 =
                     let uu____7479 =
                       FStar_TypeChecker_TcTerm.universe_of
                         g.FStar_Tactics_Types.context
                         g.FStar_Tactics_Types.goal_ty
                        in
                     FStar_Syntax_Util.mk_eq2 uu____7479
                       g.FStar_Tactics_Types.goal_ty u
                       g.FStar_Tactics_Types.witness
                      in
                   add_irrelevant_goal "dup equation"
                     g.FStar_Tactics_Types.context uu____7478
                     g.FStar_Tactics_Types.opts
                    in
                 bind uu____7475
                   (fun uu____7482  ->
                      let uu____7483 = add_goals [g']  in
                      bind uu____7483 (fun uu____7487  -> ret ())))))
  
let (flip : Prims.unit tac) =
  bind get
    (fun ps  ->
       match ps.FStar_Tactics_Types.goals with
       | g1::g2::gs ->
           set
             (let uu___121_7506 = ps  in
              {
                FStar_Tactics_Types.main_context =
                  (uu___121_7506.FStar_Tactics_Types.main_context);
                FStar_Tactics_Types.main_goal =
                  (uu___121_7506.FStar_Tactics_Types.main_goal);
                FStar_Tactics_Types.all_implicits =
                  (uu___121_7506.FStar_Tactics_Types.all_implicits);
                FStar_Tactics_Types.goals = (g2 :: g1 :: gs);
                FStar_Tactics_Types.smt_goals =
                  (uu___121_7506.FStar_Tactics_Types.smt_goals);
                FStar_Tactics_Types.depth =
                  (uu___121_7506.FStar_Tactics_Types.depth);
                FStar_Tactics_Types.__dump =
                  (uu___121_7506.FStar_Tactics_Types.__dump);
                FStar_Tactics_Types.psc =
                  (uu___121_7506.FStar_Tactics_Types.psc);
                FStar_Tactics_Types.entry_range =
                  (uu___121_7506.FStar_Tactics_Types.entry_range);
                FStar_Tactics_Types.guard_policy =
                  (uu___121_7506.FStar_Tactics_Types.guard_policy);
                FStar_Tactics_Types.freshness =
                  (uu___121_7506.FStar_Tactics_Types.freshness)
              })
       | uu____7507 -> fail "flip: less than 2 goals")
  
let (later : Prims.unit tac) =
  bind get
    (fun ps  ->
       match ps.FStar_Tactics_Types.goals with
       | [] -> ret ()
       | g::gs ->
           set
             (let uu___122_7524 = ps  in
              {
                FStar_Tactics_Types.main_context =
                  (uu___122_7524.FStar_Tactics_Types.main_context);
                FStar_Tactics_Types.main_goal =
                  (uu___122_7524.FStar_Tactics_Types.main_goal);
                FStar_Tactics_Types.all_implicits =
                  (uu___122_7524.FStar_Tactics_Types.all_implicits);
                FStar_Tactics_Types.goals = (FStar_List.append gs [g]);
                FStar_Tactics_Types.smt_goals =
                  (uu___122_7524.FStar_Tactics_Types.smt_goals);
                FStar_Tactics_Types.depth =
                  (uu___122_7524.FStar_Tactics_Types.depth);
                FStar_Tactics_Types.__dump =
                  (uu___122_7524.FStar_Tactics_Types.__dump);
                FStar_Tactics_Types.psc =
                  (uu___122_7524.FStar_Tactics_Types.psc);
                FStar_Tactics_Types.entry_range =
                  (uu___122_7524.FStar_Tactics_Types.entry_range);
                FStar_Tactics_Types.guard_policy =
                  (uu___122_7524.FStar_Tactics_Types.guard_policy);
                FStar_Tactics_Types.freshness =
                  (uu___122_7524.FStar_Tactics_Types.freshness)
              }))
  
let (qed : Prims.unit tac) =
  bind get
    (fun ps  ->
       match ps.FStar_Tactics_Types.goals with
       | [] -> ret ()
       | uu____7533 -> fail "Not done!")
  
let (cases :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 tac)
  =
  fun t  ->
    let uu____7551 =
      bind cur_goal
        (fun g  ->
           let uu____7565 = __tc g.FStar_Tactics_Types.context t  in
           bind uu____7565
             (fun uu____7601  ->
                match uu____7601 with
                | (t1,typ,guard) ->
                    let uu____7617 = FStar_Syntax_Util.head_and_args typ  in
                    (match uu____7617 with
                     | (hd1,args) ->
                         let uu____7660 =
                           let uu____7673 =
                             let uu____7674 = FStar_Syntax_Util.un_uinst hd1
                                in
                             uu____7674.FStar_Syntax_Syntax.n  in
                           (uu____7673, args)  in
                         (match uu____7660 with
                          | (FStar_Syntax_Syntax.Tm_fvar
                             fv,(p,uu____7693)::(q,uu____7695)::[]) when
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
                                let uu___123_7733 = g  in
                                let uu____7734 =
                                  FStar_TypeChecker_Env.push_bv
                                    g.FStar_Tactics_Types.context v_p
                                   in
                                {
                                  FStar_Tactics_Types.context = uu____7734;
                                  FStar_Tactics_Types.witness =
                                    (uu___123_7733.FStar_Tactics_Types.witness);
                                  FStar_Tactics_Types.goal_ty =
                                    (uu___123_7733.FStar_Tactics_Types.goal_ty);
                                  FStar_Tactics_Types.opts =
                                    (uu___123_7733.FStar_Tactics_Types.opts);
                                  FStar_Tactics_Types.is_guard =
                                    (uu___123_7733.FStar_Tactics_Types.is_guard)
                                }  in
                              let g2 =
                                let uu___124_7736 = g  in
                                let uu____7737 =
                                  FStar_TypeChecker_Env.push_bv
                                    g.FStar_Tactics_Types.context v_q
                                   in
                                {
                                  FStar_Tactics_Types.context = uu____7737;
                                  FStar_Tactics_Types.witness =
                                    (uu___124_7736.FStar_Tactics_Types.witness);
                                  FStar_Tactics_Types.goal_ty =
                                    (uu___124_7736.FStar_Tactics_Types.goal_ty);
                                  FStar_Tactics_Types.opts =
                                    (uu___124_7736.FStar_Tactics_Types.opts);
                                  FStar_Tactics_Types.is_guard =
                                    (uu___124_7736.FStar_Tactics_Types.is_guard)
                                }  in
                              bind __dismiss
                                (fun uu____7744  ->
                                   let uu____7745 = add_goals [g1; g2]  in
                                   bind uu____7745
                                     (fun uu____7754  ->
                                        let uu____7755 =
                                          let uu____7760 =
                                            FStar_Syntax_Syntax.bv_to_name
                                              v_p
                                             in
                                          let uu____7761 =
                                            FStar_Syntax_Syntax.bv_to_name
                                              v_q
                                             in
                                          (uu____7760, uu____7761)  in
                                        ret uu____7755))
                          | uu____7766 ->
                              let uu____7779 =
                                tts g.FStar_Tactics_Types.context typ  in
                              fail1 "Not a disjunction: %s" uu____7779))))
       in
    FStar_All.pipe_left (wrap_err "cases") uu____7551
  
let (set_options : Prims.string -> Prims.unit tac) =
  fun s  ->
    bind cur_goal
      (fun g  ->
         FStar_Options.push ();
         (let uu____7817 = FStar_Util.smap_copy g.FStar_Tactics_Types.opts
             in
          FStar_Options.set uu____7817);
         (let res = FStar_Options.set_options FStar_Options.Set s  in
          let opts' = FStar_Options.peek ()  in
          FStar_Options.pop ();
          (match res with
           | FStar_Getopt.Success  ->
               let g' =
                 let uu___125_7824 = g  in
                 {
                   FStar_Tactics_Types.context =
                     (uu___125_7824.FStar_Tactics_Types.context);
                   FStar_Tactics_Types.witness =
                     (uu___125_7824.FStar_Tactics_Types.witness);
                   FStar_Tactics_Types.goal_ty =
                     (uu___125_7824.FStar_Tactics_Types.goal_ty);
                   FStar_Tactics_Types.opts = opts';
                   FStar_Tactics_Types.is_guard =
                     (uu___125_7824.FStar_Tactics_Types.is_guard)
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
      let uu____7868 =
        bind cur_goal
          (fun goal  ->
             let env =
               FStar_TypeChecker_Env.set_expected_typ
                 goal.FStar_Tactics_Types.context ty
                in
             let uu____7876 = __tc env tm  in
             bind uu____7876
               (fun uu____7896  ->
                  match uu____7896 with
                  | (tm1,typ,guard) ->
                      let uu____7908 =
                        proc_guard "unquote" env guard
                          goal.FStar_Tactics_Types.opts
                         in
                      bind uu____7908 (fun uu____7912  -> ret tm1)))
         in
      FStar_All.pipe_left (wrap_err "unquote") uu____7868
  
let (uvar_env :
  env ->
    FStar_Reflection_Data.typ FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.term tac)
  =
  fun env  ->
    fun ty  ->
      let uu____7931 =
        match ty with
        | FStar_Pervasives_Native.Some ty1 -> ret ty1
        | FStar_Pervasives_Native.None  ->
            let uu____7937 =
              let uu____7938 = FStar_Syntax_Util.type_u ()  in
              FStar_All.pipe_left FStar_Pervasives_Native.fst uu____7938  in
            new_uvar "uvar_env.2" env uu____7937
         in
      bind uu____7931
        (fun typ  ->
           let uu____7950 = new_uvar "uvar_env" env typ  in
           bind uu____7950 (fun t  -> ret t))
  
let (unshelve : FStar_Syntax_Syntax.term -> Prims.unit tac) =
  fun t  ->
    let uu____7962 =
      bind get
        (fun ps  ->
           let env = ps.FStar_Tactics_Types.main_context  in
           let opts =
             match ps.FStar_Tactics_Types.goals with
             | g::uu____7973 -> g.FStar_Tactics_Types.opts
             | uu____7976 -> FStar_Options.peek ()  in
           let uu____7979 = __tc env t  in
           bind uu____7979
             (fun uu____7999  ->
                match uu____7999 with
                | (t1,typ,guard) ->
                    let uu____8011 = proc_guard "unshelve" env guard opts  in
                    bind uu____8011
                      (fun uu____8016  ->
                         let uu____8017 =
                           let uu____8020 =
                             let uu____8021 = bnorm env t1  in
                             let uu____8022 = bnorm env typ  in
                             {
                               FStar_Tactics_Types.context = env;
                               FStar_Tactics_Types.witness = uu____8021;
                               FStar_Tactics_Types.goal_ty = uu____8022;
                               FStar_Tactics_Types.opts = opts;
                               FStar_Tactics_Types.is_guard = false
                             }  in
                           [uu____8020]  in
                         add_goals uu____8017)))
       in
    FStar_All.pipe_left (wrap_err "unshelve") uu____7962
  
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
          (fun uu____8055  ->
             let uu____8056 = FStar_Options.unsafe_tactic_exec ()  in
             if uu____8056
             then
               let s =
                 FStar_Util.launch_process true "tactic_launch" prog args
                   input (fun uu____8062  -> fun uu____8063  -> false)
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
        (fun uu____8077  ->
           let uu____8078 =
             FStar_Syntax_Syntax.gen_bv nm FStar_Pervasives_Native.None t  in
           ret uu____8078)
  
let (change : FStar_Reflection_Data.typ -> Prims.unit tac) =
  fun ty  ->
    let uu____8086 =
      mlog
        (fun uu____8091  ->
           let uu____8092 = FStar_Syntax_Print.term_to_string ty  in
           FStar_Util.print1 "change: ty = %s\n" uu____8092)
        (fun uu____8094  ->
           bind cur_goal
             (fun g  ->
                let uu____8098 = __tc g.FStar_Tactics_Types.context ty  in
                bind uu____8098
                  (fun uu____8118  ->
                     match uu____8118 with
                     | (ty1,uu____8128,guard) ->
                         let uu____8130 =
                           proc_guard "change" g.FStar_Tactics_Types.context
                             guard g.FStar_Tactics_Types.opts
                            in
                         bind uu____8130
                           (fun uu____8135  ->
                              let uu____8136 =
                                do_unify g.FStar_Tactics_Types.context
                                  g.FStar_Tactics_Types.goal_ty ty1
                                 in
                              bind uu____8136
                                (fun bb  ->
                                   if bb
                                   then
                                     replace_cur
                                       (let uu___126_8145 = g  in
                                        {
                                          FStar_Tactics_Types.context =
                                            (uu___126_8145.FStar_Tactics_Types.context);
                                          FStar_Tactics_Types.witness =
                                            (uu___126_8145.FStar_Tactics_Types.witness);
                                          FStar_Tactics_Types.goal_ty = ty1;
                                          FStar_Tactics_Types.opts =
                                            (uu___126_8145.FStar_Tactics_Types.opts);
                                          FStar_Tactics_Types.is_guard =
                                            (uu___126_8145.FStar_Tactics_Types.is_guard)
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
                                      let uu____8152 =
                                        do_unify
                                          g.FStar_Tactics_Types.context ng
                                          nty
                                         in
                                      bind uu____8152
                                        (fun b  ->
                                           if b
                                           then
                                             replace_cur
                                               (let uu___127_8161 = g  in
                                                {
                                                  FStar_Tactics_Types.context
                                                    =
                                                    (uu___127_8161.FStar_Tactics_Types.context);
                                                  FStar_Tactics_Types.witness
                                                    =
                                                    (uu___127_8161.FStar_Tactics_Types.witness);
                                                  FStar_Tactics_Types.goal_ty
                                                    = ty1;
                                                  FStar_Tactics_Types.opts =
                                                    (uu___127_8161.FStar_Tactics_Types.opts);
                                                  FStar_Tactics_Types.is_guard
                                                    =
                                                    (uu___127_8161.FStar_Tactics_Types.is_guard)
                                                })
                                           else fail "not convertible")))))))
       in
    FStar_All.pipe_left (wrap_err "change") uu____8086
  
let rec last : 'a . 'a Prims.list -> 'a =
  fun l  ->
    match l with
    | [] -> failwith "last: empty list"
    | x::[] -> x
    | uu____8180::xs -> last xs
  
let rec init : 'a . 'a Prims.list -> 'a Prims.list =
  fun l  ->
    match l with
    | [] -> failwith "init: empty list"
    | x::[] -> []
    | x::xs -> let uu____8205 = init xs  in x :: uu____8205
  
let rec (inspect :
  FStar_Syntax_Syntax.term -> FStar_Reflection_Data.term_view tac) =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t  in
    let t2 = FStar_Syntax_Util.un_uinst t1  in
    match t2.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_meta (t3,uu____8220) -> inspect t3
    | FStar_Syntax_Syntax.Tm_name bv ->
        FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_Var bv)
    | FStar_Syntax_Syntax.Tm_bvar bv ->
        FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_BVar bv)
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_FVar fv)
    | FStar_Syntax_Syntax.Tm_app (hd1,[]) ->
        failwith "inspect: empty arguments on Tm_app"
    | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
        let uu____8277 = last args  in
        (match uu____8277 with
         | (a,q) ->
             let q' = FStar_Reflection_Basic.inspect_aqual q  in
             let uu____8299 =
               let uu____8300 =
                 let uu____8305 =
                   let uu____8308 =
                     let uu____8309 = init args  in
                     FStar_Syntax_Syntax.mk_Tm_app hd1 uu____8309  in
                   uu____8308 FStar_Pervasives_Native.None
                     t2.FStar_Syntax_Syntax.pos
                    in
                 (uu____8305, (a, q'))  in
               FStar_Reflection_Data.Tv_App uu____8300  in
             FStar_All.pipe_left ret uu____8299)
    | FStar_Syntax_Syntax.Tm_abs ([],uu____8330,uu____8331) ->
        failwith "inspect: empty arguments on Tm_abs"
    | FStar_Syntax_Syntax.Tm_abs (bs,t3,k) ->
        let uu____8375 = FStar_Syntax_Subst.open_term bs t3  in
        (match uu____8375 with
         | (bs1,t4) ->
             (match bs1 with
              | [] -> failwith "impossible"
              | b::bs2 ->
                  let uu____8408 =
                    let uu____8409 =
                      let uu____8414 = FStar_Syntax_Util.abs bs2 t4 k  in
                      (b, uu____8414)  in
                    FStar_Reflection_Data.Tv_Abs uu____8409  in
                  FStar_All.pipe_left ret uu____8408))
    | FStar_Syntax_Syntax.Tm_type uu____8421 ->
        FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_Type ())
    | FStar_Syntax_Syntax.Tm_arrow ([],k) ->
        failwith "inspect: empty binders on arrow"
    | FStar_Syntax_Syntax.Tm_arrow uu____8441 ->
        let uu____8454 = FStar_Syntax_Util.arrow_one t2  in
        (match uu____8454 with
         | FStar_Pervasives_Native.Some (b,c) ->
             FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_Arrow (b, c))
         | FStar_Pervasives_Native.None  -> failwith "impossible")
    | FStar_Syntax_Syntax.Tm_refine (bv,t3) ->
        let b = FStar_Syntax_Syntax.mk_binder bv  in
        let uu____8484 = FStar_Syntax_Subst.open_term [b] t3  in
        (match uu____8484 with
         | (b',t4) ->
             let b1 =
               match b' with
               | b'1::[] -> b'1
               | uu____8515 -> failwith "impossible"  in
             FStar_All.pipe_left ret
               (FStar_Reflection_Data.Tv_Refine
                  ((FStar_Pervasives_Native.fst b1), t4)))
    | FStar_Syntax_Syntax.Tm_constant c ->
        let uu____8523 =
          let uu____8524 = FStar_Reflection_Basic.inspect_const c  in
          FStar_Reflection_Data.Tv_Const uu____8524  in
        FStar_All.pipe_left ret uu____8523
    | FStar_Syntax_Syntax.Tm_uvar (u,t3) ->
        let uu____8553 =
          let uu____8554 =
            let uu____8559 =
              let uu____8560 = FStar_Syntax_Unionfind.uvar_id u  in
              FStar_BigInt.of_int_fs uu____8560  in
            (uu____8559, t3)  in
          FStar_Reflection_Data.Tv_Uvar uu____8554  in
        FStar_All.pipe_left ret uu____8553
    | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),t21) ->
        if lb.FStar_Syntax_Syntax.lbunivs <> []
        then FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
        else
          (match lb.FStar_Syntax_Syntax.lbname with
           | FStar_Util.Inr uu____8588 ->
               FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
           | FStar_Util.Inl bv ->
               let b = FStar_Syntax_Syntax.mk_binder bv  in
               let uu____8593 = FStar_Syntax_Subst.open_term [b] t21  in
               (match uu____8593 with
                | (bs,t22) ->
                    let b1 =
                      match bs with
                      | b1::[] -> b1
                      | uu____8624 ->
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
           | FStar_Util.Inr uu____8656 ->
               FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
           | FStar_Util.Inl bv ->
               let uu____8660 = FStar_Syntax_Subst.open_let_rec [lb] t21  in
               (match uu____8660 with
                | (lbs,t22) ->
                    (match lbs with
                     | lb1::[] ->
                         (match lb1.FStar_Syntax_Syntax.lbname with
                          | FStar_Util.Inr uu____8680 ->
                              ret FStar_Reflection_Data.Tv_Unknown
                          | FStar_Util.Inl bv1 ->
                              FStar_All.pipe_left ret
                                (FStar_Reflection_Data.Tv_Let
                                   (true, bv1,
                                     (lb1.FStar_Syntax_Syntax.lbdef), t22)))
                     | uu____8686 ->
                         failwith
                           "impossible: open_term returned different amount of binders")))
    | FStar_Syntax_Syntax.Tm_match (t3,brs) ->
        let rec inspect_pat p =
          match p.FStar_Syntax_Syntax.v with
          | FStar_Syntax_Syntax.Pat_constant c ->
              let uu____8738 = FStar_Reflection_Basic.inspect_const c  in
              FStar_Reflection_Data.Pat_Constant uu____8738
          | FStar_Syntax_Syntax.Pat_cons (fv,ps) ->
              let uu____8757 =
                let uu____8764 =
                  FStar_List.map
                    (fun uu____8776  ->
                       match uu____8776 with
                       | (p1,uu____8784) -> inspect_pat p1) ps
                   in
                (fv, uu____8764)  in
              FStar_Reflection_Data.Pat_Cons uu____8757
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
            (fun uu___61_8838  ->
               match uu___61_8838 with
               | (pat,uu____8860,t4) ->
                   let uu____8878 = inspect_pat pat  in (uu____8878, t4))
            brs1
           in
        FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_Match (t3, brs2))
    | FStar_Syntax_Syntax.Tm_unknown  ->
        FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
    | uu____8895 ->
        ((let uu____8897 =
            let uu____8902 =
              let uu____8903 = FStar_Syntax_Print.tag_of_term t2  in
              let uu____8904 = FStar_Syntax_Print.term_to_string t2  in
              FStar_Util.format2
                "inspect: outside of expected syntax (%s, %s)\n" uu____8903
                uu____8904
               in
            (FStar_Errors.Warning_CantInspect, uu____8902)  in
          FStar_Errors.log_issue t2.FStar_Syntax_Syntax.pos uu____8897);
         FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown)
  
let (pack : FStar_Reflection_Data.term_view -> FStar_Syntax_Syntax.term tac)
  =
  fun tv  ->
    match tv with
    | FStar_Reflection_Data.Tv_Var bv ->
        let uu____8915 = FStar_Syntax_Syntax.bv_to_name bv  in
        FStar_All.pipe_left ret uu____8915
    | FStar_Reflection_Data.Tv_BVar bv ->
        let uu____8919 = FStar_Syntax_Syntax.bv_to_tm bv  in
        FStar_All.pipe_left ret uu____8919
    | FStar_Reflection_Data.Tv_FVar fv ->
        let uu____8923 = FStar_Syntax_Syntax.fv_to_tm fv  in
        FStar_All.pipe_left ret uu____8923
    | FStar_Reflection_Data.Tv_App (l,(r,q)) ->
        let q' = FStar_Reflection_Basic.pack_aqual q  in
        let uu____8934 = FStar_Syntax_Util.mk_app l [(r, q')]  in
        FStar_All.pipe_left ret uu____8934
    | FStar_Reflection_Data.Tv_Abs (b,t) ->
        let uu____8955 =
          FStar_Syntax_Util.abs [b] t FStar_Pervasives_Native.None  in
        FStar_All.pipe_left ret uu____8955
    | FStar_Reflection_Data.Tv_Arrow (b,c) ->
        let uu____8960 = FStar_Syntax_Util.arrow [b] c  in
        FStar_All.pipe_left ret uu____8960
    | FStar_Reflection_Data.Tv_Type () ->
        FStar_All.pipe_left ret FStar_Syntax_Util.ktype
    | FStar_Reflection_Data.Tv_Refine (bv,t) ->
        let uu____8981 = FStar_Syntax_Util.refine bv t  in
        FStar_All.pipe_left ret uu____8981
    | FStar_Reflection_Data.Tv_Const c ->
        let uu____8993 =
          let uu____8996 =
            let uu____8999 =
              let uu____9000 = FStar_Reflection_Basic.pack_const c  in
              FStar_Syntax_Syntax.Tm_constant uu____9000  in
            FStar_Syntax_Syntax.mk uu____8999  in
          uu____8996 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
        FStar_All.pipe_left ret uu____8993
    | FStar_Reflection_Data.Tv_Uvar (u,t) ->
        let uu____9014 =
          let uu____9017 = FStar_BigInt.to_int_fs u  in
          FStar_Syntax_Util.uvar_from_id uu____9017 t  in
        FStar_All.pipe_left ret uu____9014
    | FStar_Reflection_Data.Tv_Let (false ,bv,t1,t2) ->
        let lb =
          FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl bv) []
            bv.FStar_Syntax_Syntax.sort FStar_Parser_Const.effect_Tot_lid t1
            [] FStar_Range.dummyRange
           in
        let uu____9032 =
          let uu____9035 =
            let uu____9038 =
              let uu____9039 =
                let uu____9052 =
                  let uu____9053 =
                    let uu____9054 = FStar_Syntax_Syntax.mk_binder bv  in
                    [uu____9054]  in
                  FStar_Syntax_Subst.close uu____9053 t2  in
                ((false, [lb]), uu____9052)  in
              FStar_Syntax_Syntax.Tm_let uu____9039  in
            FStar_Syntax_Syntax.mk uu____9038  in
          uu____9035 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
        FStar_All.pipe_left ret uu____9032
    | FStar_Reflection_Data.Tv_Let (true ,bv,t1,t2) ->
        let lb =
          FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl bv) []
            bv.FStar_Syntax_Syntax.sort FStar_Parser_Const.effect_Tot_lid t1
            [] FStar_Range.dummyRange
           in
        let uu____9080 = FStar_Syntax_Subst.open_let_rec [lb] t2  in
        (match uu____9080 with
         | (lbs_open,body_open) ->
             let uu____9095 = FStar_Syntax_Subst.close_let_rec [lb] body_open
                in
             (match uu____9095 with
              | (lbs,body) ->
                  let uu____9110 =
                    FStar_Syntax_Syntax.mk
                      (FStar_Syntax_Syntax.Tm_let ((true, lbs), body))
                      FStar_Pervasives_Native.None FStar_Range.dummyRange
                     in
                  FStar_All.pipe_left ret uu____9110))
    | FStar_Reflection_Data.Tv_Match (t,brs) ->
        let wrap v1 =
          {
            FStar_Syntax_Syntax.v = v1;
            FStar_Syntax_Syntax.p = FStar_Range.dummyRange
          }  in
        let rec pack_pat p =
          match p with
          | FStar_Reflection_Data.Pat_Constant c ->
              let uu____9146 =
                let uu____9147 = FStar_Reflection_Basic.pack_const c  in
                FStar_Syntax_Syntax.Pat_constant uu____9147  in
              FStar_All.pipe_left wrap uu____9146
          | FStar_Reflection_Data.Pat_Cons (fv,ps) ->
              let uu____9156 =
                let uu____9157 =
                  let uu____9170 =
                    FStar_List.map
                      (fun p1  ->
                         let uu____9184 = pack_pat p1  in (uu____9184, false))
                      ps
                     in
                  (fv, uu____9170)  in
                FStar_Syntax_Syntax.Pat_cons uu____9157  in
              FStar_All.pipe_left wrap uu____9156
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
            (fun uu___62_9234  ->
               match uu___62_9234 with
               | (pat,t1) ->
                   let uu____9251 = pack_pat pat  in
                   (uu____9251, FStar_Pervasives_Native.None, t1)) brs
           in
        let brs2 = FStar_List.map FStar_Syntax_Subst.close_branch brs1  in
        let uu____9261 =
          FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_match (t, brs2))
            FStar_Pervasives_Native.None FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____9261
    | FStar_Reflection_Data.Tv_AscribedT (e,t,tacopt) ->
        let uu____9281 =
          FStar_Syntax_Syntax.mk
            (FStar_Syntax_Syntax.Tm_ascribed
               (e, ((FStar_Util.Inl t), tacopt),
                 FStar_Pervasives_Native.None)) FStar_Pervasives_Native.None
            FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____9281
    | FStar_Reflection_Data.Tv_AscribedC (e,c,tacopt) ->
        let uu____9323 =
          FStar_Syntax_Syntax.mk
            (FStar_Syntax_Syntax.Tm_ascribed
               (e, ((FStar_Util.Inr c), tacopt),
                 FStar_Pervasives_Native.None)) FStar_Pervasives_Native.None
            FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____9323
    | FStar_Reflection_Data.Tv_Unknown  ->
        let uu____9358 =
          FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
            FStar_Pervasives_Native.None FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____9358
  
let (goal_of_goal_ty :
  env ->
    FStar_Reflection_Data.typ ->
      (FStar_Tactics_Types.goal,FStar_TypeChecker_Env.guard_t)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun typ  ->
      let uu____9383 =
        FStar_TypeChecker_Util.new_implicit_var "proofstate_of_goal_ty"
          typ.FStar_Syntax_Syntax.pos env typ
         in
      match uu____9383 with
      | (u,uu____9401,g_u) ->
          let g =
            let uu____9416 = FStar_Options.peek ()  in
            {
              FStar_Tactics_Types.context = env;
              FStar_Tactics_Types.witness = u;
              FStar_Tactics_Types.goal_ty = typ;
              FStar_Tactics_Types.opts = uu____9416;
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
      let uu____9427 = goal_of_goal_ty env typ  in
      match uu____9427 with
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
  