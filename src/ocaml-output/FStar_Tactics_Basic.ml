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
  
let (comp_to_typ : FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.typ) =
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
         | FStar_Tactics_Result.Failed (m,uu____830) ->
             (FStar_Syntax_Unionfind.rollback tx;
              FStar_Tactics_Result.Success ((FStar_Util.Inl m), ps)))
  
let trytac : 'a . 'a tac -> 'a FStar_Pervasives_Native.option tac =
  fun t  ->
    let uu____855 = trytac' t  in
    bind uu____855
      (fun r  ->
         match r with
         | FStar_Util.Inr v1 -> ret (FStar_Pervasives_Native.Some v1)
         | FStar_Util.Inl uu____882 -> ret FStar_Pervasives_Native.None)
  
let trytac_exn : 'a . 'a tac -> 'a FStar_Pervasives_Native.option tac =
  fun t  ->
    mk_tac
      (fun ps  ->
         try let uu____915 = trytac t  in run uu____915 ps
         with
         | FStar_Errors.Err (uu____931,msg) ->
             (log ps
                (fun uu____935  ->
                   FStar_Util.print1 "trytac_exn error: (%s)" msg);
              FStar_Tactics_Result.Success (FStar_Pervasives_Native.None, ps))
         | FStar_Errors.Error (uu____940,msg,uu____942) ->
             (log ps
                (fun uu____945  ->
                   FStar_Util.print1 "trytac_exn error: (%s)" msg);
              FStar_Tactics_Result.Success (FStar_Pervasives_Native.None, ps)))
  
let wrap_err : 'a . Prims.string -> 'a tac -> 'a tac =
  fun pref  ->
    fun t  ->
      mk_tac
        (fun ps  ->
           let uu____973 = run t ps  in
           match uu____973 with
           | FStar_Tactics_Result.Success (a,q) ->
               FStar_Tactics_Result.Success (a, q)
           | FStar_Tactics_Result.Failed (msg,q) ->
               FStar_Tactics_Result.Failed
                 ((Prims.strcat pref (Prims.strcat ": " msg)), q))
  
let (set : FStar_Tactics_Types.proofstate -> Prims.unit tac) =
  fun p  -> mk_tac (fun uu____990  -> FStar_Tactics_Result.Success ((), p)) 
let (__do_unify :
  env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool tac)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let debug_on uu____1007 =
          let uu____1008 =
            FStar_Options.set_options FStar_Options.Set
              "--debug_level Rel --debug_level RelCheck"
             in
          ()  in
        let debug_off uu____1012 =
          let uu____1013 = FStar_Options.set_options FStar_Options.Reset ""
             in
          ()  in
        (let uu____1015 =
           FStar_TypeChecker_Env.debug env (FStar_Options.Other "1346")  in
         if uu____1015
         then
           (debug_on ();
            (let uu____1017 = FStar_Syntax_Print.term_to_string t1  in
             let uu____1018 = FStar_Syntax_Print.term_to_string t2  in
             FStar_Util.print2 "%%%%%%%%do_unify %s =? %s\n" uu____1017
               uu____1018))
         else ());
        (try
           let res = FStar_TypeChecker_Rel.teq_nosmt env t1 t2  in
           debug_off (); ret res
         with
         | FStar_Errors.Err (uu____1037,msg) ->
             (debug_off ();
              mlog
                (fun uu____1041  ->
                   FStar_Util.print1 ">> do_unify error, (%s)\n" msg)
                (fun uu____1043  -> ret false))
         | FStar_Errors.Error (uu____1044,msg,r) ->
             (debug_off ();
              mlog
                (fun uu____1050  ->
                   let uu____1051 = FStar_Range.string_of_range r  in
                   FStar_Util.print2 ">> do_unify error, (%s) at (%s)\n" msg
                     uu____1051) (fun uu____1053  -> ret false)))
  
let (do_unify :
  env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool tac)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____1067 = __do_unify env t1 t2  in
        bind uu____1067
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
  
let (dismiss : Prims.unit tac) =
  bind get
    (fun p  ->
       let uu____1094 =
         let uu___63_1095 = p  in
         let uu____1096 = FStar_List.tl p.FStar_Tactics_Types.goals  in
         {
           FStar_Tactics_Types.main_context =
             (uu___63_1095.FStar_Tactics_Types.main_context);
           FStar_Tactics_Types.main_goal =
             (uu___63_1095.FStar_Tactics_Types.main_goal);
           FStar_Tactics_Types.all_implicits =
             (uu___63_1095.FStar_Tactics_Types.all_implicits);
           FStar_Tactics_Types.goals = uu____1096;
           FStar_Tactics_Types.smt_goals =
             (uu___63_1095.FStar_Tactics_Types.smt_goals);
           FStar_Tactics_Types.depth =
             (uu___63_1095.FStar_Tactics_Types.depth);
           FStar_Tactics_Types.__dump =
             (uu___63_1095.FStar_Tactics_Types.__dump);
           FStar_Tactics_Types.psc = (uu___63_1095.FStar_Tactics_Types.psc);
           FStar_Tactics_Types.entry_range =
             (uu___63_1095.FStar_Tactics_Types.entry_range);
           FStar_Tactics_Types.guard_policy =
             (uu___63_1095.FStar_Tactics_Types.guard_policy)
         }  in
       set uu____1094)
  
let (solve :
  FStar_Tactics_Types.goal -> FStar_Syntax_Syntax.term -> Prims.unit tac) =
  fun goal  ->
    fun solution  ->
      let uu____1109 = trysolve goal solution  in
      bind uu____1109
        (fun b  ->
           if b
           then dismiss
           else
             (let uu____1117 =
                let uu____1118 =
                  tts goal.FStar_Tactics_Types.context solution  in
                let uu____1119 =
                  tts goal.FStar_Tactics_Types.context
                    goal.FStar_Tactics_Types.witness
                   in
                let uu____1120 =
                  tts goal.FStar_Tactics_Types.context
                    goal.FStar_Tactics_Types.goal_ty
                   in
                FStar_Util.format3 "%s does not solve %s : %s" uu____1118
                  uu____1119 uu____1120
                 in
              fail uu____1117))
  
let (dismiss_all : Prims.unit tac) =
  bind get
    (fun p  ->
       set
         (let uu___64_1127 = p  in
          {
            FStar_Tactics_Types.main_context =
              (uu___64_1127.FStar_Tactics_Types.main_context);
            FStar_Tactics_Types.main_goal =
              (uu___64_1127.FStar_Tactics_Types.main_goal);
            FStar_Tactics_Types.all_implicits =
              (uu___64_1127.FStar_Tactics_Types.all_implicits);
            FStar_Tactics_Types.goals = [];
            FStar_Tactics_Types.smt_goals =
              (uu___64_1127.FStar_Tactics_Types.smt_goals);
            FStar_Tactics_Types.depth =
              (uu___64_1127.FStar_Tactics_Types.depth);
            FStar_Tactics_Types.__dump =
              (uu___64_1127.FStar_Tactics_Types.__dump);
            FStar_Tactics_Types.psc = (uu___64_1127.FStar_Tactics_Types.psc);
            FStar_Tactics_Types.entry_range =
              (uu___64_1127.FStar_Tactics_Types.entry_range);
            FStar_Tactics_Types.guard_policy =
              (uu___64_1127.FStar_Tactics_Types.guard_policy)
          }))
  
let (nwarn : Prims.int FStar_ST.ref) =
  FStar_Util.mk_ref (Prims.parse_int "0") 
let (check_valid_goal : FStar_Tactics_Types.goal -> Prims.unit) =
  fun g  ->
    let uu____1144 = FStar_Options.defensive ()  in
    if uu____1144
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
        let uu____1156 = FStar_TypeChecker_Env.pop_bv e  in
        match uu____1156 with
        | FStar_Pervasives_Native.None  -> b3
        | FStar_Pervasives_Native.Some (bv,e1) ->
            let b4 =
              b3 &&
                (FStar_TypeChecker_Env.closed e1 bv.FStar_Syntax_Syntax.sort)
               in
            aux b4 e1
         in
      let uu____1174 =
        (let uu____1177 = aux b2 env  in Prims.op_Negation uu____1177) &&
          (let uu____1179 = FStar_ST.op_Bang nwarn  in
           uu____1179 < (Prims.parse_int "5"))
         in
      (if uu____1174
       then
         ((let uu____1200 =
             let uu____1205 =
               let uu____1206 = goal_to_string g  in
               FStar_Util.format1
                 "The following goal is ill-formed. Keeping calm and carrying on...\n<%s>\n\n"
                 uu____1206
                in
             (FStar_Errors.Warning_IllFormedGoal, uu____1205)  in
           FStar_Errors.log_issue
             (g.FStar_Tactics_Types.goal_ty).FStar_Syntax_Syntax.pos
             uu____1200);
          (let uu____1207 =
             let uu____1208 = FStar_ST.op_Bang nwarn  in
             uu____1208 + (Prims.parse_int "1")  in
           FStar_ST.op_Colon_Equals nwarn uu____1207))
       else ())
    else ()
  
let (add_goals : FStar_Tactics_Types.goal Prims.list -> Prims.unit tac) =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___65_1266 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___65_1266.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___65_1266.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___65_1266.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (FStar_List.append gs p.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___65_1266.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___65_1266.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___65_1266.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___65_1266.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___65_1266.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___65_1266.FStar_Tactics_Types.guard_policy)
            }))
  
let (add_smt_goals : FStar_Tactics_Types.goal Prims.list -> Prims.unit tac) =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___66_1284 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___66_1284.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___66_1284.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___66_1284.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___66_1284.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (FStar_List.append gs p.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___66_1284.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___66_1284.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___66_1284.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___66_1284.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___66_1284.FStar_Tactics_Types.guard_policy)
            }))
  
let (push_goals : FStar_Tactics_Types.goal Prims.list -> Prims.unit tac) =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___67_1302 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___67_1302.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___67_1302.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___67_1302.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (FStar_List.append p.FStar_Tactics_Types.goals gs);
              FStar_Tactics_Types.smt_goals =
                (uu___67_1302.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___67_1302.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___67_1302.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___67_1302.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___67_1302.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___67_1302.FStar_Tactics_Types.guard_policy)
            }))
  
let (push_smt_goals : FStar_Tactics_Types.goal Prims.list -> Prims.unit tac)
  =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___68_1320 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___68_1320.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___68_1320.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___68_1320.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___68_1320.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (FStar_List.append p.FStar_Tactics_Types.smt_goals gs);
              FStar_Tactics_Types.depth =
                (uu___68_1320.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___68_1320.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___68_1320.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___68_1320.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___68_1320.FStar_Tactics_Types.guard_policy)
            }))
  
let (replace_cur : FStar_Tactics_Types.goal -> Prims.unit tac) =
  fun g  -> bind dismiss (fun uu____1329  -> add_goals [g]) 
let (add_implicits : implicits -> Prims.unit tac) =
  fun i  ->
    bind get
      (fun p  ->
         set
           (let uu___69_1341 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___69_1341.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___69_1341.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (FStar_List.append i p.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___69_1341.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___69_1341.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___69_1341.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___69_1341.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___69_1341.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___69_1341.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___69_1341.FStar_Tactics_Types.guard_policy)
            }))
  
let (new_uvar :
  Prims.string ->
    env -> FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.term tac)
  =
  fun reason  ->
    fun env  ->
      fun typ  ->
        let uu____1367 =
          FStar_TypeChecker_Util.new_implicit_var reason
            typ.FStar_Syntax_Syntax.pos env typ
           in
        match uu____1367 with
        | (u,uu____1383,g_u) ->
            let uu____1397 =
              add_implicits g_u.FStar_TypeChecker_Env.implicits  in
            bind uu____1397 (fun uu____1401  -> ret u)
  
let (is_true : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____1405 = FStar_Syntax_Util.un_squash t  in
    match uu____1405 with
    | FStar_Pervasives_Native.Some t' ->
        let uu____1415 =
          let uu____1416 = FStar_Syntax_Subst.compress t'  in
          uu____1416.FStar_Syntax_Syntax.n  in
        (match uu____1415 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.true_lid
         | uu____1420 -> false)
    | uu____1421 -> false
  
let (is_false : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____1429 = FStar_Syntax_Util.un_squash t  in
    match uu____1429 with
    | FStar_Pervasives_Native.Some t' ->
        let uu____1439 =
          let uu____1440 = FStar_Syntax_Subst.compress t'  in
          uu____1440.FStar_Syntax_Syntax.n  in
        (match uu____1439 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.false_lid
         | uu____1444 -> false)
    | uu____1445 -> false
  
let (cur_goal : FStar_Tactics_Types.goal tac) =
  bind get
    (fun p  ->
       match p.FStar_Tactics_Types.goals with
       | [] -> fail "No more goals (1)"
       | hd1::tl1 -> ret hd1)
  
let (is_guard : Prims.bool tac) =
  bind cur_goal (fun g  -> ret g.FStar_Tactics_Types.is_guard) 
let (mk_irrelevant_goal :
  Prims.string ->
    env ->
      FStar_Syntax_Syntax.typ ->
        FStar_Options.optionstate -> FStar_Tactics_Types.goal tac)
  =
  fun reason  ->
    fun env  ->
      fun phi  ->
        fun opts  ->
          let typ =
            let uu____1485 = env.FStar_TypeChecker_Env.universe_of env phi
               in
            FStar_Syntax_Util.mk_squash uu____1485 phi  in
          let uu____1486 = new_uvar reason env typ  in
          bind uu____1486
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
      (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.typ,FStar_TypeChecker_Env.guard_t)
        FStar_Pervasives_Native.tuple3 tac)
  =
  fun e  ->
    fun t  ->
      bind get
        (fun ps  ->
           try
             let uu____1542 =
               (ps.FStar_Tactics_Types.main_context).FStar_TypeChecker_Env.type_of
                 e t
                in
             ret uu____1542
           with
           | FStar_Errors.Err (uu____1569,msg) ->
               let uu____1571 = tts e t  in
               let uu____1572 =
                 let uu____1573 = FStar_TypeChecker_Env.all_binders e  in
                 FStar_All.pipe_right uu____1573
                   (FStar_Syntax_Print.binders_to_string ", ")
                  in
               fail3 "Cannot type %s in context (%s). Error = (%s)"
                 uu____1571 uu____1572 msg
           | FStar_Errors.Error (uu____1580,msg,uu____1582) ->
               let uu____1583 = tts e t  in
               let uu____1584 =
                 let uu____1585 = FStar_TypeChecker_Env.all_binders e  in
                 FStar_All.pipe_right uu____1585
                   (FStar_Syntax_Print.binders_to_string ", ")
                  in
               fail3 "Cannot type %s in context (%s). Error = (%s)"
                 uu____1583 uu____1584 msg)
  
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
           (let uu___72_1619 = ps  in
            {
              FStar_Tactics_Types.main_context =
                (uu___72_1619.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___72_1619.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___72_1619.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___72_1619.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___72_1619.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___72_1619.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___72_1619.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___72_1619.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___72_1619.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy = pol
            }))
  
let with_policy : 'a . FStar_Tactics_Types.guard_policy -> 'a tac -> 'a tac =
  fun pol  ->
    fun t  ->
      bind get_guard_policy
        (fun old_pol  ->
           let uu____1641 = set_guard_policy pol  in
           bind uu____1641
             (fun uu____1645  ->
                bind t
                  (fun r  ->
                     let uu____1649 = set_guard_policy old_pol  in
                     bind uu____1649 (fun uu____1653  -> ret r))))
  
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
          let uu____1670 =
            let uu____1671 = FStar_TypeChecker_Rel.simplify_guard e g  in
            uu____1671.FStar_TypeChecker_Env.guard_f  in
          match uu____1670 with
          | FStar_TypeChecker_Common.Trivial  -> ret ()
          | FStar_TypeChecker_Common.NonTrivial f ->
              let uu____1675 = istrivial e f  in
              if uu____1675
              then ret ()
              else
                bind get
                  (fun ps  ->
                     match ps.FStar_Tactics_Types.guard_policy with
                     | FStar_Tactics_Types.Drop  -> ret ()
                     | FStar_Tactics_Types.Goal  ->
                         let uu____1683 = mk_irrelevant_goal reason e f opts
                            in
                         bind uu____1683
                           (fun goal  ->
                              let goal1 =
                                let uu___73_1690 = goal  in
                                {
                                  FStar_Tactics_Types.context =
                                    (uu___73_1690.FStar_Tactics_Types.context);
                                  FStar_Tactics_Types.witness =
                                    (uu___73_1690.FStar_Tactics_Types.witness);
                                  FStar_Tactics_Types.goal_ty =
                                    (uu___73_1690.FStar_Tactics_Types.goal_ty);
                                  FStar_Tactics_Types.opts =
                                    (uu___73_1690.FStar_Tactics_Types.opts);
                                  FStar_Tactics_Types.is_guard = true
                                }  in
                              push_goals [goal1])
                     | FStar_Tactics_Types.SMT  ->
                         let uu____1691 = mk_irrelevant_goal reason e f opts
                            in
                         bind uu____1691
                           (fun goal  ->
                              let goal1 =
                                let uu___74_1698 = goal  in
                                {
                                  FStar_Tactics_Types.context =
                                    (uu___74_1698.FStar_Tactics_Types.context);
                                  FStar_Tactics_Types.witness =
                                    (uu___74_1698.FStar_Tactics_Types.witness);
                                  FStar_Tactics_Types.goal_ty =
                                    (uu___74_1698.FStar_Tactics_Types.goal_ty);
                                  FStar_Tactics_Types.opts =
                                    (uu___74_1698.FStar_Tactics_Types.opts);
                                  FStar_Tactics_Types.is_guard = true
                                }  in
                              push_smt_goals [goal1])
                     | FStar_Tactics_Types.Force  ->
                         (try
                            let uu____1706 =
                              let uu____1707 =
                                let uu____1708 =
                                  FStar_TypeChecker_Rel.discharge_guard_no_smt
                                    e g
                                   in
                                FStar_All.pipe_left
                                  FStar_TypeChecker_Rel.is_trivial uu____1708
                                 in
                              Prims.op_Negation uu____1707  in
                            if uu____1706
                            then
                              mlog
                                (fun uu____1713  ->
                                   let uu____1714 =
                                     FStar_TypeChecker_Rel.guard_to_string e
                                       g
                                      in
                                   FStar_Util.print1 "guard = %s\n"
                                     uu____1714)
                                (fun uu____1716  ->
                                   fail1 "Forcing the guard failed %s)"
                                     reason)
                            else ret ()
                          with
                          | uu____1723 ->
                              mlog
                                (fun uu____1726  ->
                                   let uu____1727 =
                                     FStar_TypeChecker_Rel.guard_to_string e
                                       g
                                      in
                                   FStar_Util.print1 "guard = %s\n"
                                     uu____1727)
                                (fun uu____1729  ->
                                   fail1 "Forcing the guard failed (%s)"
                                     reason)))
  
let (tc : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.typ tac) =
  fun t  ->
    let uu____1737 =
      bind cur_goal
        (fun goal  ->
           let uu____1743 = __tc goal.FStar_Tactics_Types.context t  in
           bind uu____1743
             (fun uu____1763  ->
                match uu____1763 with
                | (t1,typ,guard) ->
                    let uu____1775 =
                      proc_guard "tc" goal.FStar_Tactics_Types.context guard
                        goal.FStar_Tactics_Types.opts
                       in
                    bind uu____1775 (fun uu____1779  -> ret typ)))
       in
    FStar_All.pipe_left (wrap_err "tc") uu____1737
  
let (add_irrelevant_goal :
  Prims.string ->
    env ->
      FStar_Syntax_Syntax.typ -> FStar_Options.optionstate -> Prims.unit tac)
  =
  fun reason  ->
    fun env  ->
      fun phi  ->
        fun opts  ->
          let uu____1800 = mk_irrelevant_goal reason env phi opts  in
          bind uu____1800 (fun goal  -> add_goals [goal])
  
let (trivial : Prims.unit tac) =
  bind cur_goal
    (fun goal  ->
       let uu____1812 =
         istrivial goal.FStar_Tactics_Types.context
           goal.FStar_Tactics_Types.goal_ty
          in
       if uu____1812
       then solve goal FStar_Syntax_Util.exp_unit
       else
         (let uu____1816 =
            tts goal.FStar_Tactics_Types.context
              goal.FStar_Tactics_Types.goal_ty
             in
          fail1 "Not a trivial goal: %s" uu____1816))
  
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
          let uu____1837 =
            let uu____1838 = FStar_TypeChecker_Rel.simplify_guard e g  in
            uu____1838.FStar_TypeChecker_Env.guard_f  in
          match uu____1837 with
          | FStar_TypeChecker_Common.Trivial  ->
              ret FStar_Pervasives_Native.None
          | FStar_TypeChecker_Common.NonTrivial f ->
              let uu____1846 = istrivial e f  in
              if uu____1846
              then ret FStar_Pervasives_Native.None
              else
                (let uu____1854 = mk_irrelevant_goal reason e f opts  in
                 bind uu____1854
                   (fun goal  ->
                      ret
                        (FStar_Pervasives_Native.Some
                           (let uu___77_1864 = goal  in
                            {
                              FStar_Tactics_Types.context =
                                (uu___77_1864.FStar_Tactics_Types.context);
                              FStar_Tactics_Types.witness =
                                (uu___77_1864.FStar_Tactics_Types.witness);
                              FStar_Tactics_Types.goal_ty =
                                (uu___77_1864.FStar_Tactics_Types.goal_ty);
                              FStar_Tactics_Types.opts =
                                (uu___77_1864.FStar_Tactics_Types.opts);
                              FStar_Tactics_Types.is_guard = true
                            }))))
  
let (smt : Prims.unit tac) =
  bind cur_goal
    (fun g  ->
       let uu____1872 = is_irrelevant g  in
       if uu____1872
       then bind dismiss (fun uu____1876  -> add_smt_goals [g])
       else
         (let uu____1878 =
            tts g.FStar_Tactics_Types.context g.FStar_Tactics_Types.goal_ty
             in
          fail1 "goal is not irrelevant: cannot dispatch to smt (%s)"
            uu____1878))
  
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
             let uu____1919 =
               try
                 let uu____1953 =
                   let uu____1962 = FStar_BigInt.to_int_fs n1  in
                   FStar_List.splitAt uu____1962 p.FStar_Tactics_Types.goals
                    in
                 ret uu____1953
               with | uu____1984 -> fail "divide: not enough goals"  in
             bind uu____1919
               (fun uu____2011  ->
                  match uu____2011 with
                  | (lgs,rgs) ->
                      let lp =
                        let uu___78_2037 = p  in
                        {
                          FStar_Tactics_Types.main_context =
                            (uu___78_2037.FStar_Tactics_Types.main_context);
                          FStar_Tactics_Types.main_goal =
                            (uu___78_2037.FStar_Tactics_Types.main_goal);
                          FStar_Tactics_Types.all_implicits =
                            (uu___78_2037.FStar_Tactics_Types.all_implicits);
                          FStar_Tactics_Types.goals = lgs;
                          FStar_Tactics_Types.smt_goals = [];
                          FStar_Tactics_Types.depth =
                            (uu___78_2037.FStar_Tactics_Types.depth);
                          FStar_Tactics_Types.__dump =
                            (uu___78_2037.FStar_Tactics_Types.__dump);
                          FStar_Tactics_Types.psc =
                            (uu___78_2037.FStar_Tactics_Types.psc);
                          FStar_Tactics_Types.entry_range =
                            (uu___78_2037.FStar_Tactics_Types.entry_range);
                          FStar_Tactics_Types.guard_policy =
                            (uu___78_2037.FStar_Tactics_Types.guard_policy)
                        }  in
                      let rp =
                        let uu___79_2039 = p  in
                        {
                          FStar_Tactics_Types.main_context =
                            (uu___79_2039.FStar_Tactics_Types.main_context);
                          FStar_Tactics_Types.main_goal =
                            (uu___79_2039.FStar_Tactics_Types.main_goal);
                          FStar_Tactics_Types.all_implicits =
                            (uu___79_2039.FStar_Tactics_Types.all_implicits);
                          FStar_Tactics_Types.goals = rgs;
                          FStar_Tactics_Types.smt_goals = [];
                          FStar_Tactics_Types.depth =
                            (uu___79_2039.FStar_Tactics_Types.depth);
                          FStar_Tactics_Types.__dump =
                            (uu___79_2039.FStar_Tactics_Types.__dump);
                          FStar_Tactics_Types.psc =
                            (uu___79_2039.FStar_Tactics_Types.psc);
                          FStar_Tactics_Types.entry_range =
                            (uu___79_2039.FStar_Tactics_Types.entry_range);
                          FStar_Tactics_Types.guard_policy =
                            (uu___79_2039.FStar_Tactics_Types.guard_policy)
                        }  in
                      let uu____2040 = set lp  in
                      bind uu____2040
                        (fun uu____2048  ->
                           bind l
                             (fun a  ->
                                bind get
                                  (fun lp'  ->
                                     let uu____2062 = set rp  in
                                     bind uu____2062
                                       (fun uu____2070  ->
                                          bind r
                                            (fun b  ->
                                               bind get
                                                 (fun rp'  ->
                                                    let p' =
                                                      let uu___80_2086 = p
                                                         in
                                                      {
                                                        FStar_Tactics_Types.main_context
                                                          =
                                                          (uu___80_2086.FStar_Tactics_Types.main_context);
                                                        FStar_Tactics_Types.main_goal
                                                          =
                                                          (uu___80_2086.FStar_Tactics_Types.main_goal);
                                                        FStar_Tactics_Types.all_implicits
                                                          =
                                                          (uu___80_2086.FStar_Tactics_Types.all_implicits);
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
                                                          (uu___80_2086.FStar_Tactics_Types.depth);
                                                        FStar_Tactics_Types.__dump
                                                          =
                                                          (uu___80_2086.FStar_Tactics_Types.__dump);
                                                        FStar_Tactics_Types.psc
                                                          =
                                                          (uu___80_2086.FStar_Tactics_Types.psc);
                                                        FStar_Tactics_Types.entry_range
                                                          =
                                                          (uu___80_2086.FStar_Tactics_Types.entry_range);
                                                        FStar_Tactics_Types.guard_policy
                                                          =
                                                          (uu___80_2086.FStar_Tactics_Types.guard_policy)
                                                      }  in
                                                    let uu____2087 = set p'
                                                       in
                                                    bind uu____2087
                                                      (fun uu____2095  ->
                                                         ret (a, b))))))))))
  
let focus : 'a . 'a tac -> 'a tac =
  fun f  ->
    let uu____2113 = divide FStar_BigInt.one f idtac  in
    bind uu____2113
      (fun uu____2126  -> match uu____2126 with | (a,()) -> ret a)
  
let rec map : 'a . 'a tac -> 'a Prims.list tac =
  fun tau  ->
    bind get
      (fun p  ->
         match p.FStar_Tactics_Types.goals with
         | [] -> ret []
         | uu____2160::uu____2161 ->
             let uu____2164 =
               let uu____2173 = map tau  in
               divide FStar_BigInt.one tau uu____2173  in
             bind uu____2164
               (fun uu____2191  ->
                  match uu____2191 with | (h,t) -> ret (h :: t)))
  
let (seq : Prims.unit tac -> Prims.unit tac -> Prims.unit tac) =
  fun t1  ->
    fun t2  ->
      let uu____2228 =
        bind t1
          (fun uu____2233  ->
             let uu____2234 = map t2  in
             bind uu____2234 (fun uu____2242  -> ret ()))
         in
      focus uu____2228
  
let (intro : FStar_Syntax_Syntax.binder tac) =
  let uu____2249 =
    bind cur_goal
      (fun goal  ->
         let uu____2258 =
           FStar_Syntax_Util.arrow_one goal.FStar_Tactics_Types.goal_ty  in
         match uu____2258 with
         | FStar_Pervasives_Native.Some (b,c) ->
             let uu____2273 =
               let uu____2274 = FStar_Syntax_Util.is_total_comp c  in
               Prims.op_Negation uu____2274  in
             if uu____2273
             then fail "Codomain is effectful"
             else
               (let env' =
                  FStar_TypeChecker_Env.push_binders
                    goal.FStar_Tactics_Types.context [b]
                   in
                let typ' = comp_to_typ c  in
                let uu____2280 = new_uvar "intro" env' typ'  in
                bind uu____2280
                  (fun u  ->
                     let uu____2286 =
                       let uu____2289 =
                         FStar_Syntax_Util.abs [b] u
                           FStar_Pervasives_Native.None
                          in
                       trysolve goal uu____2289  in
                     bind uu____2286
                       (fun bb  ->
                          if bb
                          then
                            let uu____2295 =
                              let uu____2298 =
                                let uu___83_2299 = goal  in
                                let uu____2300 = bnorm env' u  in
                                let uu____2301 = bnorm env' typ'  in
                                {
                                  FStar_Tactics_Types.context = env';
                                  FStar_Tactics_Types.witness = uu____2300;
                                  FStar_Tactics_Types.goal_ty = uu____2301;
                                  FStar_Tactics_Types.opts =
                                    (uu___83_2299.FStar_Tactics_Types.opts);
                                  FStar_Tactics_Types.is_guard =
                                    (uu___83_2299.FStar_Tactics_Types.is_guard)
                                }  in
                              replace_cur uu____2298  in
                            bind uu____2295 (fun uu____2303  -> ret b)
                          else fail "unification failed")))
         | FStar_Pervasives_Native.None  ->
             let uu____2309 =
               tts goal.FStar_Tactics_Types.context
                 goal.FStar_Tactics_Types.goal_ty
                in
             fail1 "goal is not an arrow (%s)" uu____2309)
     in
  FStar_All.pipe_left (wrap_err "intro") uu____2249 
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
       (let uu____2340 =
          FStar_Syntax_Util.arrow_one goal.FStar_Tactics_Types.goal_ty  in
        match uu____2340 with
        | FStar_Pervasives_Native.Some (b,c) ->
            let uu____2359 =
              let uu____2360 = FStar_Syntax_Util.is_total_comp c  in
              Prims.op_Negation uu____2360  in
            if uu____2359
            then fail "Codomain is effectful"
            else
              (let bv =
                 FStar_Syntax_Syntax.gen_bv "__recf"
                   FStar_Pervasives_Native.None
                   goal.FStar_Tactics_Types.goal_ty
                  in
               let bs =
                 let uu____2376 = FStar_Syntax_Syntax.mk_binder bv  in
                 [uu____2376; b]  in
               let env' =
                 FStar_TypeChecker_Env.push_binders
                   goal.FStar_Tactics_Types.context bs
                  in
               let uu____2378 =
                 let uu____2381 = comp_to_typ c  in
                 new_uvar "intro_rec" env' uu____2381  in
               bind uu____2378
                 (fun u  ->
                    let lb =
                      let uu____2396 =
                        FStar_Syntax_Util.abs [b] u
                          FStar_Pervasives_Native.None
                         in
                      FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl bv) []
                        goal.FStar_Tactics_Types.goal_ty
                        FStar_Parser_Const.effect_Tot_lid uu____2396 []
                        FStar_Range.dummyRange
                       in
                    let body = FStar_Syntax_Syntax.bv_to_name bv  in
                    let uu____2402 =
                      FStar_Syntax_Subst.close_let_rec [lb] body  in
                    match uu____2402 with
                    | (lbs,body1) ->
                        let tm =
                          FStar_Syntax_Syntax.mk
                            (FStar_Syntax_Syntax.Tm_let ((true, lbs), body1))
                            FStar_Pervasives_Native.None
                            (goal.FStar_Tactics_Types.witness).FStar_Syntax_Syntax.pos
                           in
                        let uu____2432 = trysolve goal tm  in
                        bind uu____2432
                          (fun bb  ->
                             if bb
                             then
                               let uu____2448 =
                                 let uu____2451 =
                                   let uu___84_2452 = goal  in
                                   let uu____2453 = bnorm env' u  in
                                   let uu____2454 =
                                     let uu____2455 = comp_to_typ c  in
                                     bnorm env' uu____2455  in
                                   {
                                     FStar_Tactics_Types.context = env';
                                     FStar_Tactics_Types.witness = uu____2453;
                                     FStar_Tactics_Types.goal_ty = uu____2454;
                                     FStar_Tactics_Types.opts =
                                       (uu___84_2452.FStar_Tactics_Types.opts);
                                     FStar_Tactics_Types.is_guard =
                                       (uu___84_2452.FStar_Tactics_Types.is_guard)
                                   }  in
                                 replace_cur uu____2451  in
                               bind uu____2448
                                 (fun uu____2462  ->
                                    let uu____2463 =
                                      let uu____2468 =
                                        FStar_Syntax_Syntax.mk_binder bv  in
                                      (uu____2468, b)  in
                                    ret uu____2463)
                             else fail "intro_rec: unification failed")))
        | FStar_Pervasives_Native.None  ->
            let uu____2482 =
              tts goal.FStar_Tactics_Types.context
                goal.FStar_Tactics_Types.goal_ty
               in
            fail1 "intro_rec: goal is not an arrow (%s)" uu____2482))
  
let (norm : FStar_Syntax_Embeddings.norm_step Prims.list -> Prims.unit tac) =
  fun s  ->
    bind cur_goal
      (fun goal  ->
         mlog
           (fun uu____2502  ->
              let uu____2503 =
                FStar_Syntax_Print.term_to_string
                  goal.FStar_Tactics_Types.witness
                 in
              FStar_Util.print1 "norm: witness = %s\n" uu____2503)
           (fun uu____2508  ->
              let steps =
                let uu____2512 = FStar_TypeChecker_Normalize.tr_norm_steps s
                   in
                FStar_List.append
                  [FStar_TypeChecker_Normalize.Reify;
                  FStar_TypeChecker_Normalize.UnfoldTac] uu____2512
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
                (let uu___85_2519 = goal  in
                 {
                   FStar_Tactics_Types.context =
                     (uu___85_2519.FStar_Tactics_Types.context);
                   FStar_Tactics_Types.witness = w;
                   FStar_Tactics_Types.goal_ty = t;
                   FStar_Tactics_Types.opts =
                     (uu___85_2519.FStar_Tactics_Types.opts);
                   FStar_Tactics_Types.is_guard =
                     (uu___85_2519.FStar_Tactics_Types.is_guard)
                 })))
  
let (norm_term_env :
  env ->
    FStar_Syntax_Embeddings.norm_step Prims.list ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac)
  =
  fun e  ->
    fun s  ->
      fun t  ->
        let uu____2537 =
          mlog
            (fun uu____2542  ->
               let uu____2543 = FStar_Syntax_Print.term_to_string t  in
               FStar_Util.print1 "norm_term: tm = %s\n" uu____2543)
            (fun uu____2545  ->
               bind get
                 (fun ps  ->
                    let opts =
                      match ps.FStar_Tactics_Types.goals with
                      | g::uu____2551 -> g.FStar_Tactics_Types.opts
                      | uu____2554 -> FStar_Options.peek ()  in
                    mlog
                      (fun uu____2559  ->
                         let uu____2560 =
                           tts ps.FStar_Tactics_Types.main_context t  in
                         FStar_Util.print1 "norm_term_env: t = %s\n"
                           uu____2560)
                      (fun uu____2563  ->
                         let uu____2564 = __tc e t  in
                         bind uu____2564
                           (fun uu____2585  ->
                              match uu____2585 with
                              | (t1,uu____2595,uu____2596) ->
                                  let steps =
                                    let uu____2600 =
                                      FStar_TypeChecker_Normalize.tr_norm_steps
                                        s
                                       in
                                    FStar_List.append
                                      [FStar_TypeChecker_Normalize.Reify;
                                      FStar_TypeChecker_Normalize.UnfoldTac]
                                      uu____2600
                                     in
                                  let t2 =
                                    normalize steps
                                      ps.FStar_Tactics_Types.main_context t1
                                     in
                                  ret t2))))
           in
        FStar_All.pipe_left (wrap_err "norm_term") uu____2537
  
let (refine_intro : Prims.unit tac) =
  let uu____2612 =
    bind cur_goal
      (fun g  ->
         let uu____2619 =
           FStar_TypeChecker_Rel.base_and_refinement
             g.FStar_Tactics_Types.context g.FStar_Tactics_Types.goal_ty
            in
         match uu____2619 with
         | (uu____2632,FStar_Pervasives_Native.None ) ->
             fail "not a refinement"
         | (t,FStar_Pervasives_Native.Some (bv,phi)) ->
             let g1 =
               let uu___86_2657 = g  in
               {
                 FStar_Tactics_Types.context =
                   (uu___86_2657.FStar_Tactics_Types.context);
                 FStar_Tactics_Types.witness =
                   (uu___86_2657.FStar_Tactics_Types.witness);
                 FStar_Tactics_Types.goal_ty = t;
                 FStar_Tactics_Types.opts =
                   (uu___86_2657.FStar_Tactics_Types.opts);
                 FStar_Tactics_Types.is_guard =
                   (uu___86_2657.FStar_Tactics_Types.is_guard)
               }  in
             let uu____2658 =
               let uu____2663 =
                 let uu____2668 =
                   let uu____2669 = FStar_Syntax_Syntax.mk_binder bv  in
                   [uu____2669]  in
                 FStar_Syntax_Subst.open_term uu____2668 phi  in
               match uu____2663 with
               | (bvs,phi1) ->
                   let uu____2676 =
                     let uu____2677 = FStar_List.hd bvs  in
                     FStar_Pervasives_Native.fst uu____2677  in
                   (uu____2676, phi1)
                in
             (match uu____2658 with
              | (bv1,phi1) ->
                  let uu____2690 =
                    let uu____2693 =
                      FStar_Syntax_Subst.subst
                        [FStar_Syntax_Syntax.NT
                           (bv1, (g.FStar_Tactics_Types.witness))] phi1
                       in
                    mk_irrelevant_goal "refine_intro refinement"
                      g.FStar_Tactics_Types.context uu____2693
                      g.FStar_Tactics_Types.opts
                     in
                  bind uu____2690
                    (fun g2  ->
                       bind dismiss (fun uu____2697  -> add_goals [g1; g2]))))
     in
  FStar_All.pipe_left (wrap_err "refine_intro") uu____2612 
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
           let uu____2718 = __tc env t  in
           bind uu____2718
             (fun uu____2738  ->
                match uu____2738 with
                | (t1,typ,guard) ->
                    let uu____2750 =
                      proc_guard "__exact typing"
                        goal.FStar_Tactics_Types.context guard
                        goal.FStar_Tactics_Types.opts
                       in
                    bind uu____2750
                      (fun uu____2754  ->
                         mlog
                           (fun uu____2758  ->
                              let uu____2759 =
                                tts goal.FStar_Tactics_Types.context typ  in
                              let uu____2760 =
                                tts goal.FStar_Tactics_Types.context
                                  goal.FStar_Tactics_Types.goal_ty
                                 in
                              FStar_Util.print2 "exact: unifying %s and %s\n"
                                uu____2759 uu____2760)
                           (fun uu____2763  ->
                              let uu____2764 =
                                do_unify goal.FStar_Tactics_Types.context typ
                                  goal.FStar_Tactics_Types.goal_ty
                                 in
                              bind uu____2764
                                (fun b  ->
                                   if b
                                   then solve goal t1
                                   else
                                     (let uu____2772 =
                                        tts goal.FStar_Tactics_Types.context
                                          t1
                                         in
                                      let uu____2773 =
                                        tts goal.FStar_Tactics_Types.context
                                          typ
                                         in
                                      let uu____2774 =
                                        tts goal.FStar_Tactics_Types.context
                                          goal.FStar_Tactics_Types.goal_ty
                                         in
                                      let uu____2775 =
                                        tts goal.FStar_Tactics_Types.context
                                          goal.FStar_Tactics_Types.witness
                                         in
                                      fail4
                                        "%s : %s does not exactly solve the goal %s (witness = %s)"
                                        uu____2772 uu____2773 uu____2774
                                        uu____2775))))))
  
let (t_exact : Prims.bool -> FStar_Syntax_Syntax.term -> Prims.unit tac) =
  fun set_expected_typ1  ->
    fun tm  ->
      let uu____2786 =
        mlog
          (fun uu____2791  ->
             let uu____2792 = FStar_Syntax_Print.term_to_string tm  in
             FStar_Util.print1 "t_exact: tm = %s\n" uu____2792)
          (fun uu____2795  ->
             let uu____2796 =
               let uu____2803 = __exact_now set_expected_typ1 tm  in
               trytac' uu____2803  in
             bind uu____2796
               (fun uu___56_2812  ->
                  match uu___56_2812 with
                  | FStar_Util.Inr r -> ret ()
                  | FStar_Util.Inl e ->
                      let uu____2821 =
                        let uu____2828 =
                          let uu____2831 =
                            norm [FStar_Syntax_Embeddings.Delta]  in
                          bind uu____2831
                            (fun uu____2835  ->
                               bind refine_intro
                                 (fun uu____2837  ->
                                    __exact_now set_expected_typ1 tm))
                           in
                        trytac' uu____2828  in
                      bind uu____2821
                        (fun uu___55_2844  ->
                           match uu___55_2844 with
                           | FStar_Util.Inr r -> ret ()
                           | FStar_Util.Inl uu____2852 -> fail e)))
         in
      FStar_All.pipe_left (wrap_err "exact") uu____2786
  
let (uvar_free_in_goal :
  FStar_Syntax_Syntax.uvar -> FStar_Tactics_Types.goal -> Prims.bool) =
  fun u  ->
    fun g  ->
      if g.FStar_Tactics_Types.is_guard
      then false
      else
        (let free_uvars =
           let uu____2867 =
             let uu____2874 =
               FStar_Syntax_Free.uvars g.FStar_Tactics_Types.goal_ty  in
             FStar_Util.set_elements uu____2874  in
           FStar_List.map FStar_Pervasives_Native.fst uu____2867  in
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
          let uu____2934 = f x  in
          bind uu____2934
            (fun y  ->
               let uu____2942 = mapM f xs  in
               bind uu____2942 (fun ys  -> ret (y :: ys)))
  
exception NoUnif 
let (uu___is_NoUnif : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with | NoUnif  -> true | uu____2960 -> false
  
let rec (__apply :
  Prims.bool ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.typ -> Prims.unit tac)
  =
  fun uopt  ->
    fun tm  ->
      fun typ  ->
        bind cur_goal
          (fun goal  ->
             mlog
               (fun uu____2978  ->
                  let uu____2979 = FStar_Syntax_Print.term_to_string tm  in
                  FStar_Util.print1 ">>> Calling __exact(%s)\n" uu____2979)
               (fun uu____2982  ->
                  let uu____2983 =
                    let uu____2988 =
                      let uu____2991 = t_exact false tm  in
                      with_policy FStar_Tactics_Types.Force uu____2991  in
                    trytac_exn uu____2988  in
                  bind uu____2983
                    (fun uu___57_2998  ->
                       match uu___57_2998 with
                       | FStar_Pervasives_Native.Some r -> ret ()
                       | FStar_Pervasives_Native.None  ->
                           mlog
                             (fun uu____3006  ->
                                let uu____3007 =
                                  FStar_Syntax_Print.term_to_string typ  in
                                FStar_Util.print1 ">>> typ = %s\n" uu____3007)
                             (fun uu____3010  ->
                                let uu____3011 =
                                  FStar_Syntax_Util.arrow_one typ  in
                                match uu____3011 with
                                | FStar_Pervasives_Native.None  ->
                                    FStar_Exn.raise NoUnif
                                | FStar_Pervasives_Native.Some ((bv,aq),c) ->
                                    mlog
                                      (fun uu____3043  ->
                                         let uu____3044 =
                                           FStar_Syntax_Print.binder_to_string
                                             (bv, aq)
                                            in
                                         FStar_Util.print1
                                           "__apply: pushing binder %s\n"
                                           uu____3044)
                                      (fun uu____3047  ->
                                         let uu____3048 =
                                           let uu____3049 =
                                             FStar_Syntax_Util.is_total_comp
                                               c
                                              in
                                           Prims.op_Negation uu____3049  in
                                         if uu____3048
                                         then
                                           fail "apply: not total codomain"
                                         else
                                           (let uu____3053 =
                                              new_uvar "apply"
                                                goal.FStar_Tactics_Types.context
                                                bv.FStar_Syntax_Syntax.sort
                                               in
                                            bind uu____3053
                                              (fun u  ->
                                                 let tm' =
                                                   FStar_Syntax_Syntax.mk_Tm_app
                                                     tm [(u, aq)]
                                                     FStar_Pervasives_Native.None
                                                     tm.FStar_Syntax_Syntax.pos
                                                    in
                                                 let typ' =
                                                   let uu____3073 =
                                                     comp_to_typ c  in
                                                   FStar_All.pipe_left
                                                     (FStar_Syntax_Subst.subst
                                                        [FStar_Syntax_Syntax.NT
                                                           (bv, u)])
                                                     uu____3073
                                                    in
                                                 let uu____3074 =
                                                   __apply uopt tm' typ'  in
                                                 bind uu____3074
                                                   (fun uu____3082  ->
                                                      let u1 =
                                                        bnorm
                                                          goal.FStar_Tactics_Types.context
                                                          u
                                                         in
                                                      let uu____3084 =
                                                        let uu____3085 =
                                                          let uu____3088 =
                                                            let uu____3089 =
                                                              FStar_Syntax_Util.head_and_args
                                                                u1
                                                               in
                                                            FStar_Pervasives_Native.fst
                                                              uu____3089
                                                             in
                                                          FStar_Syntax_Subst.compress
                                                            uu____3088
                                                           in
                                                        uu____3085.FStar_Syntax_Syntax.n
                                                         in
                                                      match uu____3084 with
                                                      | FStar_Syntax_Syntax.Tm_uvar
                                                          (uvar,uu____3117)
                                                          ->
                                                          bind get
                                                            (fun ps  ->
                                                               let uu____3145
                                                                 =
                                                                 uopt &&
                                                                   (uvar_free
                                                                    uvar ps)
                                                                  in
                                                               if uu____3145
                                                               then ret ()
                                                               else
                                                                 (let uu____3149
                                                                    =
                                                                    let uu____3152
                                                                    =
                                                                    let uu___87_3153
                                                                    = goal
                                                                     in
                                                                    let uu____3154
                                                                    =
                                                                    bnorm
                                                                    goal.FStar_Tactics_Types.context
                                                                    u1  in
                                                                    let uu____3155
                                                                    =
                                                                    bnorm
                                                                    goal.FStar_Tactics_Types.context
                                                                    bv.FStar_Syntax_Syntax.sort
                                                                     in
                                                                    {
                                                                    FStar_Tactics_Types.context
                                                                    =
                                                                    (uu___87_3153.FStar_Tactics_Types.context);
                                                                    FStar_Tactics_Types.witness
                                                                    =
                                                                    uu____3154;
                                                                    FStar_Tactics_Types.goal_ty
                                                                    =
                                                                    uu____3155;
                                                                    FStar_Tactics_Types.opts
                                                                    =
                                                                    (uu___87_3153.FStar_Tactics_Types.opts);
                                                                    FStar_Tactics_Types.is_guard
                                                                    = false
                                                                    }  in
                                                                    [uu____3152]
                                                                     in
                                                                  add_goals
                                                                    uu____3149))
                                                      | t -> ret ()))))))))
  
let try_unif : 'a . 'a tac -> 'a tac -> 'a tac =
  fun t  ->
    fun t'  -> mk_tac (fun ps  -> try run t ps with | NoUnif  -> run t' ps)
  
let (apply : Prims.bool -> FStar_Syntax_Syntax.term -> Prims.unit tac) =
  fun uopt  ->
    fun tm  ->
      let uu____3201 =
        mlog
          (fun uu____3206  ->
             let uu____3207 = FStar_Syntax_Print.term_to_string tm  in
             FStar_Util.print1 "apply: tm = %s\n" uu____3207)
          (fun uu____3209  ->
             bind cur_goal
               (fun goal  ->
                  let uu____3213 = __tc goal.FStar_Tactics_Types.context tm
                     in
                  bind uu____3213
                    (fun uu____3235  ->
                       match uu____3235 with
                       | (tm1,typ,guard) ->
                           let typ1 =
                             bnorm goal.FStar_Tactics_Types.context typ  in
                           let uu____3248 =
                             let uu____3251 =
                               let uu____3254 = __apply uopt tm1 typ1  in
                               bind uu____3254
                                 (fun uu____3258  ->
                                    proc_guard "apply guard"
                                      goal.FStar_Tactics_Types.context guard
                                      goal.FStar_Tactics_Types.opts)
                                in
                             focus uu____3251  in
                           let uu____3259 =
                             let uu____3262 =
                               tts goal.FStar_Tactics_Types.context tm1  in
                             let uu____3263 =
                               tts goal.FStar_Tactics_Types.context typ1  in
                             let uu____3264 =
                               tts goal.FStar_Tactics_Types.context
                                 goal.FStar_Tactics_Types.goal_ty
                                in
                             fail3
                               "Cannot instantiate %s (of type %s) to match goal (%s)"
                               uu____3262 uu____3263 uu____3264
                              in
                           try_unif uu____3248 uu____3259)))
         in
      FStar_All.pipe_left (wrap_err "apply") uu____3201
  
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
      let uu____3291 =
        match ct.FStar_Syntax_Syntax.effect_args with
        | pre::post::uu____3310 ->
            ((FStar_Pervasives_Native.fst pre),
              (FStar_Pervasives_Native.fst post))
        | uu____3351 -> failwith "apply_lemma: impossible: not a lemma"  in
      match uu____3291 with
      | (pre,post) ->
          let post1 =
            let uu____3387 =
              let uu____3396 =
                FStar_Syntax_Syntax.as_arg FStar_Syntax_Util.exp_unit  in
              [uu____3396]  in
            FStar_Syntax_Util.mk_app post uu____3387  in
          FStar_Pervasives_Native.Some (pre, post1)
    else
      if FStar_Syntax_Util.is_pure_effect ct.FStar_Syntax_Syntax.effect_name
      then
        (let uu____3416 =
           FStar_Syntax_Util.un_squash ct.FStar_Syntax_Syntax.result_typ  in
         FStar_Util.map_opt uu____3416
           (fun post  -> (FStar_Syntax_Util.t_true, post)))
      else FStar_Pervasives_Native.None
  
let (apply_lemma : FStar_Syntax_Syntax.term -> Prims.unit tac) =
  fun tm  ->
    let uu____3447 =
      let uu____3450 =
        mlog
          (fun uu____3455  ->
             let uu____3456 = FStar_Syntax_Print.term_to_string tm  in
             FStar_Util.print1 "apply_lemma: tm = %s\n" uu____3456)
          (fun uu____3459  ->
             let is_unit_t t =
               let uu____3464 =
                 let uu____3465 = FStar_Syntax_Subst.compress t  in
                 uu____3465.FStar_Syntax_Syntax.n  in
               match uu____3464 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.unit_lid
                   -> true
               | uu____3469 -> false  in
             bind cur_goal
               (fun goal  ->
                  let uu____3473 = __tc goal.FStar_Tactics_Types.context tm
                     in
                  bind uu____3473
                    (fun uu____3496  ->
                       match uu____3496 with
                       | (tm1,t,guard) ->
                           let uu____3508 =
                             FStar_Syntax_Util.arrow_formals_comp t  in
                           (match uu____3508 with
                            | (bs,comp) ->
                                let uu____3535 = lemma_or_sq comp  in
                                (match uu____3535 with
                                 | FStar_Pervasives_Native.None  ->
                                     fail "not a lemma or squashed function"
                                 | FStar_Pervasives_Native.Some (pre,post) ->
                                     let uu____3554 =
                                       FStar_List.fold_left
                                         (fun uu____3600  ->
                                            fun uu____3601  ->
                                              match (uu____3600, uu____3601)
                                              with
                                              | ((uvs,guard1,subst1),(b,aq))
                                                  ->
                                                  let b_t =
                                                    FStar_Syntax_Subst.subst
                                                      subst1
                                                      b.FStar_Syntax_Syntax.sort
                                                     in
                                                  let uu____3704 =
                                                    is_unit_t b_t  in
                                                  if uu____3704
                                                  then
                                                    (((FStar_Syntax_Util.exp_unit,
                                                        aq) :: uvs), guard1,
                                                      ((FStar_Syntax_Syntax.NT
                                                          (b,
                                                            FStar_Syntax_Util.exp_unit))
                                                      :: subst1))
                                                  else
                                                    (let uu____3742 =
                                                       FStar_TypeChecker_Util.new_implicit_var
                                                         "apply_lemma"
                                                         (goal.FStar_Tactics_Types.goal_ty).FStar_Syntax_Syntax.pos
                                                         goal.FStar_Tactics_Types.context
                                                         b_t
                                                        in
                                                     match uu____3742 with
                                                     | (u,uu____3772,g_u) ->
                                                         let uu____3786 =
                                                           FStar_TypeChecker_Rel.conj_guard
                                                             guard1 g_u
                                                            in
                                                         (((u, aq) :: uvs),
                                                           uu____3786,
                                                           ((FStar_Syntax_Syntax.NT
                                                               (b, u)) ::
                                                           subst1))))
                                         ([], guard, []) bs
                                        in
                                     (match uu____3554 with
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
                                          let uu____3857 =
                                            let uu____3860 =
                                              FStar_Syntax_Util.mk_squash
                                                FStar_Syntax_Syntax.U_zero
                                                post1
                                               in
                                            do_unify
                                              goal.FStar_Tactics_Types.context
                                              uu____3860
                                              goal.FStar_Tactics_Types.goal_ty
                                             in
                                          bind uu____3857
                                            (fun b  ->
                                               if Prims.op_Negation b
                                               then
                                                 let uu____3868 =
                                                   tts
                                                     goal.FStar_Tactics_Types.context
                                                     tm1
                                                    in
                                                 let uu____3869 =
                                                   let uu____3870 =
                                                     FStar_Syntax_Util.mk_squash
                                                       FStar_Syntax_Syntax.U_zero
                                                       post1
                                                      in
                                                   tts
                                                     goal.FStar_Tactics_Types.context
                                                     uu____3870
                                                    in
                                                 let uu____3871 =
                                                   tts
                                                     goal.FStar_Tactics_Types.context
                                                     goal.FStar_Tactics_Types.goal_ty
                                                    in
                                                 fail3
                                                   "Cannot instantiate lemma %s (with postcondition: %s) to match goal (%s)"
                                                   uu____3868 uu____3869
                                                   uu____3871
                                               else
                                                 (let uu____3873 =
                                                    add_implicits
                                                      implicits.FStar_TypeChecker_Env.implicits
                                                     in
                                                  bind uu____3873
                                                    (fun uu____3878  ->
                                                       let uu____3879 =
                                                         solve goal
                                                           FStar_Syntax_Util.exp_unit
                                                          in
                                                       bind uu____3879
                                                         (fun uu____3887  ->
                                                            let is_free_uvar
                                                              uv t1 =
                                                              let free_uvars
                                                                =
                                                                let uu____3898
                                                                  =
                                                                  let uu____3905
                                                                    =
                                                                    FStar_Syntax_Free.uvars
                                                                    t1  in
                                                                  FStar_Util.set_elements
                                                                    uu____3905
                                                                   in
                                                                FStar_List.map
                                                                  FStar_Pervasives_Native.fst
                                                                  uu____3898
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
                                                              let uu____3946
                                                                =
                                                                FStar_Syntax_Util.head_and_args
                                                                  t1
                                                                 in
                                                              match uu____3946
                                                              with
                                                              | (hd1,uu____3962)
                                                                  ->
                                                                  (match 
                                                                    hd1.FStar_Syntax_Syntax.n
                                                                   with
                                                                   | 
                                                                   FStar_Syntax_Syntax.Tm_uvar
                                                                    (uv,uu____3984)
                                                                    ->
                                                                    appears
                                                                    uv goals
                                                                   | 
                                                                   uu____4009
                                                                    -> false)
                                                               in
                                                            let uu____4010 =
                                                              FStar_All.pipe_right
                                                                implicits.FStar_TypeChecker_Env.implicits
                                                                (mapM
                                                                   (fun
                                                                    uu____4082
                                                                     ->
                                                                    match uu____4082
                                                                    with
                                                                    | 
                                                                    (_msg,env,_uvar,term,typ,uu____4110)
                                                                    ->
                                                                    let uu____4111
                                                                    =
                                                                    FStar_Syntax_Util.head_and_args
                                                                    term  in
                                                                    (match uu____4111
                                                                    with
                                                                    | 
                                                                    (hd1,uu____4137)
                                                                    ->
                                                                    let uu____4158
                                                                    =
                                                                    let uu____4159
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    hd1  in
                                                                    uu____4159.FStar_Syntax_Syntax.n
                                                                     in
                                                                    (match uu____4158
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Tm_uvar
                                                                    uu____4172
                                                                    ->
                                                                    let uu____4189
                                                                    =
                                                                    let uu____4198
                                                                    =
                                                                    let uu____4201
                                                                    =
                                                                    let uu___90_4202
                                                                    = goal
                                                                     in
                                                                    let uu____4203
                                                                    =
                                                                    bnorm
                                                                    goal.FStar_Tactics_Types.context
                                                                    term  in
                                                                    let uu____4204
                                                                    =
                                                                    bnorm
                                                                    goal.FStar_Tactics_Types.context
                                                                    typ  in
                                                                    {
                                                                    FStar_Tactics_Types.context
                                                                    =
                                                                    (uu___90_4202.FStar_Tactics_Types.context);
                                                                    FStar_Tactics_Types.witness
                                                                    =
                                                                    uu____4203;
                                                                    FStar_Tactics_Types.goal_ty
                                                                    =
                                                                    uu____4204;
                                                                    FStar_Tactics_Types.opts
                                                                    =
                                                                    (uu___90_4202.FStar_Tactics_Types.opts);
                                                                    FStar_Tactics_Types.is_guard
                                                                    =
                                                                    (uu___90_4202.FStar_Tactics_Types.is_guard)
                                                                    }  in
                                                                    [uu____4201]
                                                                     in
                                                                    (uu____4198,
                                                                    [])  in
                                                                    ret
                                                                    uu____4189
                                                                    | 
                                                                    uu____4217
                                                                    ->
                                                                    let g_typ
                                                                    =
                                                                    let uu____4219
                                                                    =
                                                                    FStar_Options.__temp_fast_implicits
                                                                    ()  in
                                                                    if
                                                                    uu____4219
                                                                    then
                                                                    FStar_TypeChecker_TcTerm.check_type_of_well_typed_term
                                                                    false env
                                                                    term typ
                                                                    else
                                                                    (let term1
                                                                    =
                                                                    bnorm env
                                                                    term  in
                                                                    let uu____4222
                                                                    =
                                                                    let uu____4229
                                                                    =
                                                                    FStar_TypeChecker_Env.set_expected_typ
                                                                    env typ
                                                                     in
                                                                    env.FStar_TypeChecker_Env.type_of
                                                                    uu____4229
                                                                    term1  in
                                                                    match uu____4222
                                                                    with
                                                                    | 
                                                                    (uu____4230,uu____4231,g_typ)
                                                                    -> g_typ)
                                                                     in
                                                                    let uu____4233
                                                                    =
                                                                    goal_from_guard
                                                                    "apply_lemma solved arg"
                                                                    goal.FStar_Tactics_Types.context
                                                                    g_typ
                                                                    goal.FStar_Tactics_Types.opts
                                                                     in
                                                                    bind
                                                                    uu____4233
                                                                    (fun
                                                                    uu___58_4249
                                                                     ->
                                                                    match uu___58_4249
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
                                                            bind uu____4010
                                                              (fun goals_  ->
                                                                 let sub_goals
                                                                   =
                                                                   let uu____4317
                                                                    =
                                                                    FStar_List.map
                                                                    FStar_Pervasives_Native.fst
                                                                    goals_
                                                                     in
                                                                   FStar_List.flatten
                                                                    uu____4317
                                                                    in
                                                                 let smt_goals
                                                                   =
                                                                   let uu____4339
                                                                    =
                                                                    FStar_List.map
                                                                    FStar_Pervasives_Native.snd
                                                                    goals_
                                                                     in
                                                                   FStar_List.flatten
                                                                    uu____4339
                                                                    in
                                                                 let rec filter'
                                                                   a f xs =
                                                                   match xs
                                                                   with
                                                                   | 
                                                                   [] -> []
                                                                   | 
                                                                   x::xs1 ->
                                                                    let uu____4394
                                                                    = f x xs1
                                                                     in
                                                                    if
                                                                    uu____4394
                                                                    then
                                                                    let uu____4397
                                                                    =
                                                                    filter'
                                                                    () f xs1
                                                                     in x ::
                                                                    uu____4397
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
                                                                    let uu____4411
                                                                    =
                                                                    checkone
                                                                    g.FStar_Tactics_Types.witness
                                                                    goals  in
                                                                    Prims.op_Negation
                                                                    uu____4411))
                                                                    a438 a439)
                                                                    (Obj.magic
                                                                    sub_goals))
                                                                    in
                                                                 let uu____4412
                                                                   =
                                                                   proc_guard
                                                                    "apply_lemma guard"
                                                                    goal.FStar_Tactics_Types.context
                                                                    guard
                                                                    goal.FStar_Tactics_Types.opts
                                                                    in
                                                                 bind
                                                                   uu____4412
                                                                   (fun
                                                                    uu____4417
                                                                     ->
                                                                    let uu____4418
                                                                    =
                                                                    let uu____4421
                                                                    =
                                                                    let uu____4422
                                                                    =
                                                                    let uu____4423
                                                                    =
                                                                    FStar_Syntax_Util.mk_squash
                                                                    FStar_Syntax_Syntax.U_zero
                                                                    pre1  in
                                                                    istrivial
                                                                    goal.FStar_Tactics_Types.context
                                                                    uu____4423
                                                                     in
                                                                    Prims.op_Negation
                                                                    uu____4422
                                                                     in
                                                                    if
                                                                    uu____4421
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
                                                                    uu____4418
                                                                    (fun
                                                                    uu____4429
                                                                     ->
                                                                    let uu____4430
                                                                    =
                                                                    add_smt_goals
                                                                    smt_goals
                                                                     in
                                                                    bind
                                                                    uu____4430
                                                                    (fun
                                                                    uu____4434
                                                                     ->
                                                                    add_goals
                                                                    sub_goals1))))))))))))))
         in
      focus uu____3450  in
    FStar_All.pipe_left (wrap_err "apply_lemma") uu____3447
  
let (destruct_eq' :
  FStar_Syntax_Syntax.typ ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun typ  ->
    let uu____4454 = FStar_Syntax_Util.destruct_typ_as_formula typ  in
    match uu____4454 with
    | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn
        (l,uu____4464::(e1,uu____4466)::(e2,uu____4468)::[])) when
        FStar_Ident.lid_equals l FStar_Parser_Const.eq2_lid ->
        FStar_Pervasives_Native.Some (e1, e2)
    | uu____4527 -> FStar_Pervasives_Native.None
  
let (destruct_eq :
  FStar_Syntax_Syntax.typ ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun typ  ->
    let uu____4549 = destruct_eq' typ  in
    match uu____4549 with
    | FStar_Pervasives_Native.Some t -> FStar_Pervasives_Native.Some t
    | FStar_Pervasives_Native.None  ->
        let uu____4579 = FStar_Syntax_Util.un_squash typ  in
        (match uu____4579 with
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
        let uu____4635 = FStar_TypeChecker_Env.pop_bv e1  in
        match uu____4635 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (bv',e') ->
            if FStar_Syntax_Syntax.bv_eq bvar bv'
            then FStar_Pervasives_Native.Some (e', [])
            else
              (let uu____4683 = aux e'  in
               FStar_Util.map_opt uu____4683
                 (fun uu____4707  ->
                    match uu____4707 with | (e'',bvs) -> (e'', (bv' :: bvs))))
         in
      let uu____4728 = aux e  in
      FStar_Util.map_opt uu____4728
        (fun uu____4752  ->
           match uu____4752 with | (e',bvs) -> (e', (FStar_List.rev bvs)))
  
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
          let uu____4807 = split_env b1 g.FStar_Tactics_Types.context  in
          FStar_Util.map_opt uu____4807
            (fun uu____4831  ->
               match uu____4831 with
               | (e0,bvs) ->
                   let s1 bv =
                     let uu___91_4848 = bv  in
                     let uu____4849 =
                       FStar_Syntax_Subst.subst s bv.FStar_Syntax_Syntax.sort
                        in
                     {
                       FStar_Syntax_Syntax.ppname =
                         (uu___91_4848.FStar_Syntax_Syntax.ppname);
                       FStar_Syntax_Syntax.index =
                         (uu___91_4848.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort = uu____4849
                     }  in
                   let bvs1 = FStar_List.map s1 bvs  in
                   let c = push_bvs e0 (b2 :: bvs1)  in
                   let w =
                     FStar_Syntax_Subst.subst s g.FStar_Tactics_Types.witness
                      in
                   let t =
                     FStar_Syntax_Subst.subst s g.FStar_Tactics_Types.goal_ty
                      in
                   let uu___92_4858 = g  in
                   {
                     FStar_Tactics_Types.context = c;
                     FStar_Tactics_Types.witness = w;
                     FStar_Tactics_Types.goal_ty = t;
                     FStar_Tactics_Types.opts =
                       (uu___92_4858.FStar_Tactics_Types.opts);
                     FStar_Tactics_Types.is_guard =
                       (uu___92_4858.FStar_Tactics_Types.is_guard)
                   })
  
let (rewrite : FStar_Syntax_Syntax.binder -> Prims.unit tac) =
  fun h  ->
    bind cur_goal
      (fun goal  ->
         let uu____4871 = h  in
         match uu____4871 with
         | (bv,uu____4875) ->
             mlog
               (fun uu____4879  ->
                  let uu____4880 = FStar_Syntax_Print.bv_to_string bv  in
                  let uu____4881 =
                    tts goal.FStar_Tactics_Types.context
                      bv.FStar_Syntax_Syntax.sort
                     in
                  FStar_Util.print2 "+++Rewrite %s : %s\n" uu____4880
                    uu____4881)
               (fun uu____4884  ->
                  let uu____4885 =
                    split_env bv goal.FStar_Tactics_Types.context  in
                  match uu____4885 with
                  | FStar_Pervasives_Native.None  ->
                      fail "rewrite: binder not found in environment"
                  | FStar_Pervasives_Native.Some (e0,bvs) ->
                      let uu____4914 =
                        destruct_eq bv.FStar_Syntax_Syntax.sort  in
                      (match uu____4914 with
                       | FStar_Pervasives_Native.Some (x,e) ->
                           let uu____4929 =
                             let uu____4930 = FStar_Syntax_Subst.compress x
                                in
                             uu____4930.FStar_Syntax_Syntax.n  in
                           (match uu____4929 with
                            | FStar_Syntax_Syntax.Tm_name x1 ->
                                let s = [FStar_Syntax_Syntax.NT (x1, e)]  in
                                let s1 bv1 =
                                  let uu___93_4943 = bv1  in
                                  let uu____4944 =
                                    FStar_Syntax_Subst.subst s
                                      bv1.FStar_Syntax_Syntax.sort
                                     in
                                  {
                                    FStar_Syntax_Syntax.ppname =
                                      (uu___93_4943.FStar_Syntax_Syntax.ppname);
                                    FStar_Syntax_Syntax.index =
                                      (uu___93_4943.FStar_Syntax_Syntax.index);
                                    FStar_Syntax_Syntax.sort = uu____4944
                                  }  in
                                let bvs1 = FStar_List.map s1 bvs  in
                                let uu____4950 =
                                  let uu___94_4951 = goal  in
                                  let uu____4952 = push_bvs e0 (bv :: bvs1)
                                     in
                                  let uu____4953 =
                                    FStar_Syntax_Subst.subst s
                                      goal.FStar_Tactics_Types.witness
                                     in
                                  let uu____4954 =
                                    FStar_Syntax_Subst.subst s
                                      goal.FStar_Tactics_Types.goal_ty
                                     in
                                  {
                                    FStar_Tactics_Types.context = uu____4952;
                                    FStar_Tactics_Types.witness = uu____4953;
                                    FStar_Tactics_Types.goal_ty = uu____4954;
                                    FStar_Tactics_Types.opts =
                                      (uu___94_4951.FStar_Tactics_Types.opts);
                                    FStar_Tactics_Types.is_guard =
                                      (uu___94_4951.FStar_Tactics_Types.is_guard)
                                  }  in
                                replace_cur uu____4950
                            | uu____4955 ->
                                fail
                                  "rewrite: Not an equality hypothesis with a variable on the LHS")
                       | uu____4956 ->
                           fail "rewrite: Not an equality hypothesis")))
  
let (rename_to :
  FStar_Syntax_Syntax.binder -> Prims.string -> Prims.unit tac) =
  fun b  ->
    fun s  ->
      bind cur_goal
        (fun goal  ->
           let uu____4981 = b  in
           match uu____4981 with
           | (bv,uu____4985) ->
               let bv' =
                 FStar_Syntax_Syntax.freshen_bv
                   (let uu___95_4989 = bv  in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (FStar_Ident.mk_ident
                           (s,
                             ((bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange)));
                      FStar_Syntax_Syntax.index =
                        (uu___95_4989.FStar_Syntax_Syntax.index);
                      FStar_Syntax_Syntax.sort =
                        (uu___95_4989.FStar_Syntax_Syntax.sort)
                    })
                  in
               let s1 =
                 let uu____4993 =
                   let uu____4994 =
                     let uu____5001 = FStar_Syntax_Syntax.bv_to_name bv'  in
                     (bv, uu____5001)  in
                   FStar_Syntax_Syntax.NT uu____4994  in
                 [uu____4993]  in
               let uu____5002 = subst_goal bv bv' s1 goal  in
               (match uu____5002 with
                | FStar_Pervasives_Native.None  ->
                    fail "rename_to: binder not found in environment"
                | FStar_Pervasives_Native.Some goal1 -> replace_cur goal1))
  
let (binder_retype : FStar_Syntax_Syntax.binder -> Prims.unit tac) =
  fun b  ->
    bind cur_goal
      (fun goal  ->
         let uu____5021 = b  in
         match uu____5021 with
         | (bv,uu____5025) ->
             let uu____5026 = split_env bv goal.FStar_Tactics_Types.context
                in
             (match uu____5026 with
              | FStar_Pervasives_Native.None  ->
                  fail "binder_retype: binder is not present in environment"
              | FStar_Pervasives_Native.Some (e0,bvs) ->
                  let uu____5055 = FStar_Syntax_Util.type_u ()  in
                  (match uu____5055 with
                   | (ty,u) ->
                       let uu____5064 = new_uvar "binder_retype" e0 ty  in
                       bind uu____5064
                         (fun t'  ->
                            let bv'' =
                              let uu___96_5074 = bv  in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___96_5074.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___96_5074.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = t'
                              }  in
                            let s =
                              let uu____5078 =
                                let uu____5079 =
                                  let uu____5086 =
                                    FStar_Syntax_Syntax.bv_to_name bv''  in
                                  (bv, uu____5086)  in
                                FStar_Syntax_Syntax.NT uu____5079  in
                              [uu____5078]  in
                            let bvs1 =
                              FStar_List.map
                                (fun b1  ->
                                   let uu___97_5094 = b1  in
                                   let uu____5095 =
                                     FStar_Syntax_Subst.subst s
                                       b1.FStar_Syntax_Syntax.sort
                                      in
                                   {
                                     FStar_Syntax_Syntax.ppname =
                                       (uu___97_5094.FStar_Syntax_Syntax.ppname);
                                     FStar_Syntax_Syntax.index =
                                       (uu___97_5094.FStar_Syntax_Syntax.index);
                                     FStar_Syntax_Syntax.sort = uu____5095
                                   }) bvs
                               in
                            let env' = push_bvs e0 (bv'' :: bvs1)  in
                            bind dismiss
                              (fun uu____5101  ->
                                 let uu____5102 =
                                   let uu____5105 =
                                     let uu____5108 =
                                       let uu___98_5109 = goal  in
                                       let uu____5110 =
                                         FStar_Syntax_Subst.subst s
                                           goal.FStar_Tactics_Types.witness
                                          in
                                       let uu____5111 =
                                         FStar_Syntax_Subst.subst s
                                           goal.FStar_Tactics_Types.goal_ty
                                          in
                                       {
                                         FStar_Tactics_Types.context = env';
                                         FStar_Tactics_Types.witness =
                                           uu____5110;
                                         FStar_Tactics_Types.goal_ty =
                                           uu____5111;
                                         FStar_Tactics_Types.opts =
                                           (uu___98_5109.FStar_Tactics_Types.opts);
                                         FStar_Tactics_Types.is_guard =
                                           (uu___98_5109.FStar_Tactics_Types.is_guard)
                                       }  in
                                     [uu____5108]  in
                                   add_goals uu____5105  in
                                 bind uu____5102
                                   (fun uu____5114  ->
                                      let uu____5115 =
                                        FStar_Syntax_Util.mk_eq2
                                          (FStar_Syntax_Syntax.U_succ u) ty
                                          bv.FStar_Syntax_Syntax.sort t'
                                         in
                                      add_irrelevant_goal
                                        "binder_retype equation" e0
                                        uu____5115
                                        goal.FStar_Tactics_Types.opts))))))
  
let (norm_binder_type :
  FStar_Syntax_Embeddings.norm_step Prims.list ->
    FStar_Syntax_Syntax.binder -> Prims.unit tac)
  =
  fun s  ->
    fun b  ->
      bind cur_goal
        (fun goal  ->
           let uu____5136 = b  in
           match uu____5136 with
           | (bv,uu____5140) ->
               let uu____5141 = split_env bv goal.FStar_Tactics_Types.context
                  in
               (match uu____5141 with
                | FStar_Pervasives_Native.None  ->
                    fail
                      "binder_retype: binder is not present in environment"
                | FStar_Pervasives_Native.Some (e0,bvs) ->
                    let steps =
                      let uu____5173 =
                        FStar_TypeChecker_Normalize.tr_norm_steps s  in
                      FStar_List.append
                        [FStar_TypeChecker_Normalize.Reify;
                        FStar_TypeChecker_Normalize.UnfoldTac] uu____5173
                       in
                    let sort' =
                      normalize steps e0 bv.FStar_Syntax_Syntax.sort  in
                    let bv' =
                      let uu___99_5178 = bv  in
                      {
                        FStar_Syntax_Syntax.ppname =
                          (uu___99_5178.FStar_Syntax_Syntax.ppname);
                        FStar_Syntax_Syntax.index =
                          (uu___99_5178.FStar_Syntax_Syntax.index);
                        FStar_Syntax_Syntax.sort = sort'
                      }  in
                    let env' = push_bvs e0 (bv' :: bvs)  in
                    replace_cur
                      (let uu___100_5182 = goal  in
                       {
                         FStar_Tactics_Types.context = env';
                         FStar_Tactics_Types.witness =
                           (uu___100_5182.FStar_Tactics_Types.witness);
                         FStar_Tactics_Types.goal_ty =
                           (uu___100_5182.FStar_Tactics_Types.goal_ty);
                         FStar_Tactics_Types.opts =
                           (uu___100_5182.FStar_Tactics_Types.opts);
                         FStar_Tactics_Types.is_guard =
                           (uu___100_5182.FStar_Tactics_Types.is_guard)
                       })))
  
let (revert : Prims.unit tac) =
  bind cur_goal
    (fun goal  ->
       let uu____5190 =
         FStar_TypeChecker_Env.pop_bv goal.FStar_Tactics_Types.context  in
       match uu____5190 with
       | FStar_Pervasives_Native.None  -> fail "Cannot revert; empty context"
       | FStar_Pervasives_Native.Some (x,env') ->
           let typ' =
             let uu____5212 =
               FStar_Syntax_Syntax.mk_Total goal.FStar_Tactics_Types.goal_ty
                in
             FStar_Syntax_Util.arrow [(x, FStar_Pervasives_Native.None)]
               uu____5212
              in
           let w' =
             FStar_Syntax_Util.abs [(x, FStar_Pervasives_Native.None)]
               goal.FStar_Tactics_Types.witness FStar_Pervasives_Native.None
              in
           replace_cur
             (let uu___101_5246 = goal  in
              {
                FStar_Tactics_Types.context = env';
                FStar_Tactics_Types.witness = w';
                FStar_Tactics_Types.goal_ty = typ';
                FStar_Tactics_Types.opts =
                  (uu___101_5246.FStar_Tactics_Types.opts);
                FStar_Tactics_Types.is_guard =
                  (uu___101_5246.FStar_Tactics_Types.is_guard)
              }))
  
let (free_in :
  FStar_Syntax_Syntax.bv -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun bv  ->
    fun t  ->
      let uu____5253 = FStar_Syntax_Free.names t  in
      FStar_Util.set_mem bv uu____5253
  
let rec (clear : FStar_Syntax_Syntax.binder -> Prims.unit tac) =
  fun b  ->
    let bv = FStar_Pervasives_Native.fst b  in
    bind cur_goal
      (fun goal  ->
         mlog
           (fun uu____5269  ->
              let uu____5270 = FStar_Syntax_Print.binder_to_string b  in
              let uu____5271 =
                let uu____5272 =
                  let uu____5273 =
                    FStar_TypeChecker_Env.all_binders
                      goal.FStar_Tactics_Types.context
                     in
                  FStar_All.pipe_right uu____5273 FStar_List.length  in
                FStar_All.pipe_right uu____5272 FStar_Util.string_of_int  in
              FStar_Util.print2 "Clear of (%s), env has %s binders\n"
                uu____5270 uu____5271)
           (fun uu____5284  ->
              let uu____5285 = split_env bv goal.FStar_Tactics_Types.context
                 in
              match uu____5285 with
              | FStar_Pervasives_Native.None  ->
                  fail "Cannot clear; binder not in environment"
              | FStar_Pervasives_Native.Some (e',bvs) ->
                  let rec check1 bvs1 =
                    match bvs1 with
                    | [] -> ret ()
                    | bv'::bvs2 ->
                        let uu____5330 =
                          free_in bv bv'.FStar_Syntax_Syntax.sort  in
                        if uu____5330
                        then
                          let uu____5333 =
                            let uu____5334 =
                              FStar_Syntax_Print.bv_to_string bv'  in
                            FStar_Util.format1
                              "Cannot clear; binder present in the type of %s"
                              uu____5334
                             in
                          fail uu____5333
                        else check1 bvs2
                     in
                  let uu____5336 =
                    free_in bv goal.FStar_Tactics_Types.goal_ty  in
                  if uu____5336
                  then fail "Cannot clear; binder present in goal"
                  else
                    (let uu____5340 = check1 bvs  in
                     bind uu____5340
                       (fun uu____5346  ->
                          let env' = push_bvs e' bvs  in
                          let uu____5348 =
                            new_uvar "clear.witness" env'
                              goal.FStar_Tactics_Types.goal_ty
                             in
                          bind uu____5348
                            (fun ut  ->
                               let uu____5354 =
                                 do_unify goal.FStar_Tactics_Types.context
                                   goal.FStar_Tactics_Types.witness ut
                                  in
                               bind uu____5354
                                 (fun b1  ->
                                    if b1
                                    then
                                      replace_cur
                                        (let uu___102_5363 = goal  in
                                         {
                                           FStar_Tactics_Types.context = env';
                                           FStar_Tactics_Types.witness = ut;
                                           FStar_Tactics_Types.goal_ty =
                                             (uu___102_5363.FStar_Tactics_Types.goal_ty);
                                           FStar_Tactics_Types.opts =
                                             (uu___102_5363.FStar_Tactics_Types.opts);
                                           FStar_Tactics_Types.is_guard =
                                             (uu___102_5363.FStar_Tactics_Types.is_guard)
                                         })
                                    else
                                      fail
                                        "Cannot clear; binder appears in witness"))))))
  
let (clear_top : Prims.unit tac) =
  bind cur_goal
    (fun goal  ->
       let uu____5372 =
         FStar_TypeChecker_Env.pop_bv goal.FStar_Tactics_Types.context  in
       match uu____5372 with
       | FStar_Pervasives_Native.None  -> fail "Cannot clear; empty context"
       | FStar_Pervasives_Native.Some (x,uu____5386) ->
           let uu____5391 = FStar_Syntax_Syntax.mk_binder x  in
           clear uu____5391)
  
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
           let uu___103_5407 = g  in
           {
             FStar_Tactics_Types.context = ctx';
             FStar_Tactics_Types.witness =
               (uu___103_5407.FStar_Tactics_Types.witness);
             FStar_Tactics_Types.goal_ty =
               (uu___103_5407.FStar_Tactics_Types.goal_ty);
             FStar_Tactics_Types.opts =
               (uu___103_5407.FStar_Tactics_Types.opts);
             FStar_Tactics_Types.is_guard =
               (uu___103_5407.FStar_Tactics_Types.is_guard)
           }  in
         bind dismiss (fun uu____5409  -> add_goals [g']))
  
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
           let uu___104_5425 = g  in
           {
             FStar_Tactics_Types.context = ctx';
             FStar_Tactics_Types.witness =
               (uu___104_5425.FStar_Tactics_Types.witness);
             FStar_Tactics_Types.goal_ty =
               (uu___104_5425.FStar_Tactics_Types.goal_ty);
             FStar_Tactics_Types.opts =
               (uu___104_5425.FStar_Tactics_Types.opts);
             FStar_Tactics_Types.is_guard =
               (uu___104_5425.FStar_Tactics_Types.is_guard)
           }  in
         bind dismiss (fun uu____5427  -> add_goals [g']))
  
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
            let uu____5459 = FStar_Syntax_Subst.compress t  in
            uu____5459.FStar_Syntax_Syntax.n  in
          let uu____5462 =
            if d = FStar_Tactics_Types.TopDown
            then
              f env
                (let uu___108_5468 = t  in
                 {
                   FStar_Syntax_Syntax.n = tn;
                   FStar_Syntax_Syntax.pos =
                     (uu___108_5468.FStar_Syntax_Syntax.pos);
                   FStar_Syntax_Syntax.vars =
                     (uu___108_5468.FStar_Syntax_Syntax.vars)
                 })
            else ret t  in
          bind uu____5462
            (fun t1  ->
               let ff = tac_fold_env d f env  in
               let tn1 =
                 let uu____5482 =
                   let uu____5483 = FStar_Syntax_Subst.compress t1  in
                   uu____5483.FStar_Syntax_Syntax.n  in
                 match uu____5482 with
                 | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
                     let uu____5510 = ff hd1  in
                     bind uu____5510
                       (fun hd2  ->
                          let fa uu____5530 =
                            match uu____5530 with
                            | (a,q) ->
                                let uu____5543 = ff a  in
                                bind uu____5543 (fun a1  -> ret (a1, q))
                             in
                          let uu____5556 = mapM fa args  in
                          bind uu____5556
                            (fun args1  ->
                               ret (FStar_Syntax_Syntax.Tm_app (hd2, args1))))
                 | FStar_Syntax_Syntax.Tm_abs (bs,t2,k) ->
                     let uu____5616 = FStar_Syntax_Subst.open_term bs t2  in
                     (match uu____5616 with
                      | (bs1,t') ->
                          let uu____5625 =
                            let uu____5628 =
                              FStar_TypeChecker_Env.push_binders env bs1  in
                            tac_fold_env d f uu____5628 t'  in
                          bind uu____5625
                            (fun t''  ->
                               let uu____5632 =
                                 let uu____5633 =
                                   let uu____5650 =
                                     FStar_Syntax_Subst.close_binders bs1  in
                                   let uu____5651 =
                                     FStar_Syntax_Subst.close bs1 t''  in
                                   (uu____5650, uu____5651, k)  in
                                 FStar_Syntax_Syntax.Tm_abs uu____5633  in
                               ret uu____5632))
                 | FStar_Syntax_Syntax.Tm_arrow (bs,k) -> ret tn
                 | FStar_Syntax_Syntax.Tm_match (hd1,brs) ->
                     let uu____5710 = ff hd1  in
                     bind uu____5710
                       (fun hd2  ->
                          let ffb br =
                            let uu____5723 =
                              FStar_Syntax_Subst.open_branch br  in
                            match uu____5723 with
                            | (pat,w,e) ->
                                let uu____5745 = ff e  in
                                bind uu____5745
                                  (fun e1  ->
                                     let br1 =
                                       FStar_Syntax_Subst.close_branch
                                         (pat, w, e1)
                                        in
                                     ret br1)
                             in
                          let uu____5758 = mapM ffb brs  in
                          bind uu____5758
                            (fun brs1  ->
                               ret (FStar_Syntax_Syntax.Tm_match (hd2, brs1))))
                 | FStar_Syntax_Syntax.Tm_let
                     ((false
                       ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl bv;
                          FStar_Syntax_Syntax.lbunivs = uu____5772;
                          FStar_Syntax_Syntax.lbtyp = uu____5773;
                          FStar_Syntax_Syntax.lbeff = uu____5774;
                          FStar_Syntax_Syntax.lbdef = def;
                          FStar_Syntax_Syntax.lbattrs = uu____5776;
                          FStar_Syntax_Syntax.lbpos = uu____5777;_}::[]),e)
                     ->
                     let lb =
                       let uu____5802 =
                         let uu____5803 = FStar_Syntax_Subst.compress t1  in
                         uu____5803.FStar_Syntax_Syntax.n  in
                       match uu____5802 with
                       | FStar_Syntax_Syntax.Tm_let
                           ((false ,lb::[]),uu____5807) -> lb
                       | uu____5820 -> failwith "impossible"  in
                     let fflb lb1 =
                       let uu____5827 = ff lb1.FStar_Syntax_Syntax.lbdef  in
                       bind uu____5827
                         (fun def1  ->
                            ret
                              (let uu___105_5833 = lb1  in
                               {
                                 FStar_Syntax_Syntax.lbname =
                                   (uu___105_5833.FStar_Syntax_Syntax.lbname);
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___105_5833.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp =
                                   (uu___105_5833.FStar_Syntax_Syntax.lbtyp);
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___105_5833.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def1;
                                 FStar_Syntax_Syntax.lbattrs =
                                   (uu___105_5833.FStar_Syntax_Syntax.lbattrs);
                                 FStar_Syntax_Syntax.lbpos =
                                   (uu___105_5833.FStar_Syntax_Syntax.lbpos)
                               }))
                        in
                     let uu____5834 = fflb lb  in
                     bind uu____5834
                       (fun lb1  ->
                          let uu____5843 =
                            let uu____5848 =
                              let uu____5849 =
                                FStar_Syntax_Syntax.mk_binder bv  in
                              [uu____5849]  in
                            FStar_Syntax_Subst.open_term uu____5848 e  in
                          match uu____5843 with
                          | (bs,e1) ->
                              let uu____5854 = ff e1  in
                              bind uu____5854
                                (fun e2  ->
                                   let e3 = FStar_Syntax_Subst.close bs e2
                                      in
                                   ret
                                     (FStar_Syntax_Syntax.Tm_let
                                        ((false, [lb1]), e3))))
                 | FStar_Syntax_Syntax.Tm_let ((true ,lbs),e) ->
                     let fflb lb =
                       let uu____5891 = ff lb.FStar_Syntax_Syntax.lbdef  in
                       bind uu____5891
                         (fun def  ->
                            ret
                              (let uu___106_5897 = lb  in
                               {
                                 FStar_Syntax_Syntax.lbname =
                                   (uu___106_5897.FStar_Syntax_Syntax.lbname);
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___106_5897.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp =
                                   (uu___106_5897.FStar_Syntax_Syntax.lbtyp);
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___106_5897.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def;
                                 FStar_Syntax_Syntax.lbattrs =
                                   (uu___106_5897.FStar_Syntax_Syntax.lbattrs);
                                 FStar_Syntax_Syntax.lbpos =
                                   (uu___106_5897.FStar_Syntax_Syntax.lbpos)
                               }))
                        in
                     let uu____5898 = FStar_Syntax_Subst.open_let_rec lbs e
                        in
                     (match uu____5898 with
                      | (lbs1,e1) ->
                          let uu____5913 = mapM fflb lbs1  in
                          bind uu____5913
                            (fun lbs2  ->
                               let uu____5925 = ff e1  in
                               bind uu____5925
                                 (fun e2  ->
                                    let uu____5933 =
                                      FStar_Syntax_Subst.close_let_rec lbs2
                                        e2
                                       in
                                    match uu____5933 with
                                    | (lbs3,e3) ->
                                        ret
                                          (FStar_Syntax_Syntax.Tm_let
                                             ((true, lbs3), e3)))))
                 | FStar_Syntax_Syntax.Tm_ascribed (t2,asc,eff) ->
                     let uu____5999 = ff t2  in
                     bind uu____5999
                       (fun t3  ->
                          ret
                            (FStar_Syntax_Syntax.Tm_ascribed (t3, asc, eff)))
                 | FStar_Syntax_Syntax.Tm_meta (t2,m) ->
                     let uu____6028 = ff t2  in
                     bind uu____6028
                       (fun t3  -> ret (FStar_Syntax_Syntax.Tm_meta (t3, m)))
                 | uu____6033 -> ret tn  in
               bind tn1
                 (fun tn2  ->
                    let t' =
                      let uu___107_6040 = t1  in
                      {
                        FStar_Syntax_Syntax.n = tn2;
                        FStar_Syntax_Syntax.pos =
                          (uu___107_6040.FStar_Syntax_Syntax.pos);
                        FStar_Syntax_Syntax.vars =
                          (uu___107_6040.FStar_Syntax_Syntax.vars)
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
            let uu____6069 = FStar_TypeChecker_TcTerm.tc_term env t  in
            match uu____6069 with
            | (t1,lcomp,g) ->
                let uu____6081 =
                  (let uu____6084 =
                     FStar_Syntax_Util.is_pure_or_ghost_lcomp lcomp  in
                   Prims.op_Negation uu____6084) ||
                    (let uu____6086 = FStar_TypeChecker_Rel.is_trivial g  in
                     Prims.op_Negation uu____6086)
                   in
                if uu____6081
                then ret t1
                else
                  (let rewrite_eq =
                     let typ = lcomp.FStar_Syntax_Syntax.res_typ  in
                     let uu____6096 = new_uvar "pointwise_rec" env typ  in
                     bind uu____6096
                       (fun ut  ->
                          log ps
                            (fun uu____6107  ->
                               let uu____6108 =
                                 FStar_Syntax_Print.term_to_string t1  in
                               let uu____6109 =
                                 FStar_Syntax_Print.term_to_string ut  in
                               FStar_Util.print2
                                 "Pointwise_rec: making equality\n\t%s ==\n\t%s\n"
                                 uu____6108 uu____6109);
                          (let uu____6110 =
                             let uu____6113 =
                               let uu____6114 =
                                 FStar_TypeChecker_TcTerm.universe_of env typ
                                  in
                               FStar_Syntax_Util.mk_eq2 uu____6114 typ t1 ut
                                in
                             add_irrelevant_goal "pointwise_rec equation" env
                               uu____6113 opts
                              in
                           bind uu____6110
                             (fun uu____6117  ->
                                let uu____6118 =
                                  bind tau
                                    (fun uu____6124  ->
                                       let ut1 =
                                         FStar_TypeChecker_Normalize.reduce_uvar_solutions
                                           env ut
                                          in
                                       log ps
                                         (fun uu____6130  ->
                                            let uu____6131 =
                                              FStar_Syntax_Print.term_to_string
                                                t1
                                               in
                                            let uu____6132 =
                                              FStar_Syntax_Print.term_to_string
                                                ut1
                                               in
                                            FStar_Util.print2
                                              "Pointwise_rec: succeeded rewriting\n\t%s to\n\t%s\n"
                                              uu____6131 uu____6132);
                                       ret ut1)
                                   in
                                focus uu____6118)))
                      in
                   let uu____6133 = trytac' rewrite_eq  in
                   bind uu____6133
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
          let uu____6281 = FStar_Syntax_Subst.compress t  in
          maybe_continue ctrl uu____6281
            (fun t1  ->
               let uu____6285 =
                 f env
                   (let uu___111_6294 = t1  in
                    {
                      FStar_Syntax_Syntax.n = (t1.FStar_Syntax_Syntax.n);
                      FStar_Syntax_Syntax.pos =
                        (uu___111_6294.FStar_Syntax_Syntax.pos);
                      FStar_Syntax_Syntax.vars =
                        (uu___111_6294.FStar_Syntax_Syntax.vars)
                    })
                  in
               bind uu____6285
                 (fun uu____6306  ->
                    match uu____6306 with
                    | (t2,ctrl1) ->
                        maybe_continue ctrl1 t2
                          (fun t3  ->
                             let uu____6325 =
                               let uu____6326 =
                                 FStar_Syntax_Subst.compress t3  in
                               uu____6326.FStar_Syntax_Syntax.n  in
                             match uu____6325 with
                             | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
                                 let uu____6359 =
                                   ctrl_tac_fold f env ctrl1 hd1  in
                                 bind uu____6359
                                   (fun uu____6384  ->
                                      match uu____6384 with
                                      | (hd2,ctrl2) ->
                                          let ctrl3 = keep_going ctrl2  in
                                          let uu____6400 =
                                            ctrl_tac_fold_args f env ctrl3
                                              args
                                             in
                                          bind uu____6400
                                            (fun uu____6427  ->
                                               match uu____6427 with
                                               | (args1,ctrl4) ->
                                                   ret
                                                     ((let uu___109_6457 = t3
                                                          in
                                                       {
                                                         FStar_Syntax_Syntax.n
                                                           =
                                                           (FStar_Syntax_Syntax.Tm_app
                                                              (hd2, args1));
                                                         FStar_Syntax_Syntax.pos
                                                           =
                                                           (uu___109_6457.FStar_Syntax_Syntax.pos);
                                                         FStar_Syntax_Syntax.vars
                                                           =
                                                           (uu___109_6457.FStar_Syntax_Syntax.vars)
                                                       }), ctrl4)))
                             | FStar_Syntax_Syntax.Tm_abs (bs,t4,k) ->
                                 let uu____6483 =
                                   FStar_Syntax_Subst.open_term bs t4  in
                                 (match uu____6483 with
                                  | (bs1,t') ->
                                      let uu____6498 =
                                        let uu____6505 =
                                          FStar_TypeChecker_Env.push_binders
                                            env bs1
                                           in
                                        ctrl_tac_fold f uu____6505 ctrl1 t'
                                         in
                                      bind uu____6498
                                        (fun uu____6523  ->
                                           match uu____6523 with
                                           | (t'',ctrl2) ->
                                               let uu____6538 =
                                                 let uu____6545 =
                                                   let uu___110_6548 = t4  in
                                                   let uu____6551 =
                                                     let uu____6552 =
                                                       let uu____6569 =
                                                         FStar_Syntax_Subst.close_binders
                                                           bs1
                                                          in
                                                       let uu____6570 =
                                                         FStar_Syntax_Subst.close
                                                           bs1 t''
                                                          in
                                                       (uu____6569,
                                                         uu____6570, k)
                                                        in
                                                     FStar_Syntax_Syntax.Tm_abs
                                                       uu____6552
                                                      in
                                                   {
                                                     FStar_Syntax_Syntax.n =
                                                       uu____6551;
                                                     FStar_Syntax_Syntax.pos
                                                       =
                                                       (uu___110_6548.FStar_Syntax_Syntax.pos);
                                                     FStar_Syntax_Syntax.vars
                                                       =
                                                       (uu___110_6548.FStar_Syntax_Syntax.vars)
                                                   }  in
                                                 (uu____6545, ctrl2)  in
                                               ret uu____6538))
                             | FStar_Syntax_Syntax.Tm_arrow (bs,k) ->
                                 ret (t3, ctrl1)
                             | uu____6603 -> ret (t3, ctrl1))))

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
              let uu____6654 = ctrl_tac_fold f env ctrl t  in
              bind uu____6654
                (fun uu____6682  ->
                   match uu____6682 with
                   | (t1,ctrl1) ->
                       let uu____6701 = ctrl_tac_fold_args f env ctrl1 ts1
                          in
                       bind uu____6701
                         (fun uu____6732  ->
                            match uu____6732 with
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
              let uu____6816 =
                let uu____6823 =
                  add_irrelevant_goal "dummy" env FStar_Syntax_Util.t_true
                    opts
                   in
                bind uu____6823
                  (fun uu____6832  ->
                     let uu____6833 = ctrl t1  in
                     bind uu____6833
                       (fun res  -> bind trivial (fun uu____6860  -> ret res)))
                 in
              bind uu____6816
                (fun uu____6876  ->
                   match uu____6876 with
                   | (should_rewrite,ctrl1) ->
                       if Prims.op_Negation should_rewrite
                       then ret (t1, ctrl1)
                       else
                         (let uu____6900 =
                            FStar_TypeChecker_TcTerm.tc_term env t1  in
                          match uu____6900 with
                          | (t2,lcomp,g) ->
                              let uu____6916 =
                                (let uu____6919 =
                                   FStar_Syntax_Util.is_pure_or_ghost_lcomp
                                     lcomp
                                    in
                                 Prims.op_Negation uu____6919) ||
                                  (let uu____6921 =
                                     FStar_TypeChecker_Rel.is_trivial g  in
                                   Prims.op_Negation uu____6921)
                                 in
                              if uu____6916
                              then ret (t2, globalStop)
                              else
                                (let typ = lcomp.FStar_Syntax_Syntax.res_typ
                                    in
                                 let uu____6936 =
                                   new_uvar "pointwise_rec" env typ  in
                                 bind uu____6936
                                   (fun ut  ->
                                      log ps
                                        (fun uu____6951  ->
                                           let uu____6952 =
                                             FStar_Syntax_Print.term_to_string
                                               t2
                                              in
                                           let uu____6953 =
                                             FStar_Syntax_Print.term_to_string
                                               ut
                                              in
                                           FStar_Util.print2
                                             "Pointwise_rec: making equality\n\t%s ==\n\t%s\n"
                                             uu____6952 uu____6953);
                                      (let uu____6954 =
                                         let uu____6957 =
                                           let uu____6958 =
                                             FStar_TypeChecker_TcTerm.universe_of
                                               env typ
                                              in
                                           FStar_Syntax_Util.mk_eq2
                                             uu____6958 typ t2 ut
                                            in
                                         add_irrelevant_goal
                                           "rewrite_rec equation" env
                                           uu____6957 opts
                                          in
                                       bind uu____6954
                                         (fun uu____6965  ->
                                            let uu____6966 =
                                              bind rewriter
                                                (fun uu____6980  ->
                                                   let ut1 =
                                                     FStar_TypeChecker_Normalize.reduce_uvar_solutions
                                                       env ut
                                                      in
                                                   log ps
                                                     (fun uu____6986  ->
                                                        let uu____6987 =
                                                          FStar_Syntax_Print.term_to_string
                                                            t2
                                                           in
                                                        let uu____6988 =
                                                          FStar_Syntax_Print.term_to_string
                                                            ut1
                                                           in
                                                        FStar_Util.print2
                                                          "rewrite_rec: succeeded rewriting\n\t%s to\n\t%s\n"
                                                          uu____6987
                                                          uu____6988);
                                                   ret (ut1, ctrl1))
                                               in
                                            focus uu____6966))))))
  
let (topdown_rewrite :
  (FStar_Syntax_Syntax.term ->
     (Prims.bool,FStar_BigInt.t) FStar_Pervasives_Native.tuple2 tac)
    -> Prims.unit tac -> Prims.unit tac)
  =
  fun ctrl  ->
    fun rewriter  ->
      bind get
        (fun ps  ->
           let uu____7032 =
             match ps.FStar_Tactics_Types.goals with
             | g::gs -> (g, gs)
             | [] -> failwith "Pointwise: no goals"  in
           match uu____7032 with
           | (g,gs) ->
               let gt1 = g.FStar_Tactics_Types.goal_ty  in
               (log ps
                  (fun uu____7069  ->
                     let uu____7070 = FStar_Syntax_Print.term_to_string gt1
                        in
                     FStar_Util.print1 "Pointwise starting with %s\n"
                       uu____7070);
                bind dismiss_all
                  (fun uu____7073  ->
                     let uu____7074 =
                       ctrl_tac_fold
                         (rewrite_rec ps ctrl rewriter
                            g.FStar_Tactics_Types.opts)
                         g.FStar_Tactics_Types.context keepGoing gt1
                        in
                     bind uu____7074
                       (fun uu____7092  ->
                          match uu____7092 with
                          | (gt',uu____7100) ->
                              (log ps
                                 (fun uu____7104  ->
                                    let uu____7105 =
                                      FStar_Syntax_Print.term_to_string gt'
                                       in
                                    FStar_Util.print1
                                      "Pointwise seems to have succeded with %s\n"
                                      uu____7105);
                               (let uu____7106 = push_goals gs  in
                                bind uu____7106
                                  (fun uu____7110  ->
                                     add_goals
                                       [(let uu___112_7112 = g  in
                                         {
                                           FStar_Tactics_Types.context =
                                             (uu___112_7112.FStar_Tactics_Types.context);
                                           FStar_Tactics_Types.witness =
                                             (uu___112_7112.FStar_Tactics_Types.witness);
                                           FStar_Tactics_Types.goal_ty = gt';
                                           FStar_Tactics_Types.opts =
                                             (uu___112_7112.FStar_Tactics_Types.opts);
                                           FStar_Tactics_Types.is_guard =
                                             (uu___112_7112.FStar_Tactics_Types.is_guard)
                                         })])))))))
  
let (pointwise :
  FStar_Tactics_Types.direction -> Prims.unit tac -> Prims.unit tac) =
  fun d  ->
    fun tau  ->
      bind get
        (fun ps  ->
           let uu____7134 =
             match ps.FStar_Tactics_Types.goals with
             | g::gs -> (g, gs)
             | [] -> failwith "Pointwise: no goals"  in
           match uu____7134 with
           | (g,gs) ->
               let gt1 = g.FStar_Tactics_Types.goal_ty  in
               (log ps
                  (fun uu____7171  ->
                     let uu____7172 = FStar_Syntax_Print.term_to_string gt1
                        in
                     FStar_Util.print1 "Pointwise starting with %s\n"
                       uu____7172);
                bind dismiss_all
                  (fun uu____7175  ->
                     let uu____7176 =
                       tac_fold_env d
                         (pointwise_rec ps tau g.FStar_Tactics_Types.opts)
                         g.FStar_Tactics_Types.context gt1
                        in
                     bind uu____7176
                       (fun gt'  ->
                          log ps
                            (fun uu____7186  ->
                               let uu____7187 =
                                 FStar_Syntax_Print.term_to_string gt'  in
                               FStar_Util.print1
                                 "Pointwise seems to have succeded with %s\n"
                                 uu____7187);
                          (let uu____7188 = push_goals gs  in
                           bind uu____7188
                             (fun uu____7192  ->
                                add_goals
                                  [(let uu___113_7194 = g  in
                                    {
                                      FStar_Tactics_Types.context =
                                        (uu___113_7194.FStar_Tactics_Types.context);
                                      FStar_Tactics_Types.witness =
                                        (uu___113_7194.FStar_Tactics_Types.witness);
                                      FStar_Tactics_Types.goal_ty = gt';
                                      FStar_Tactics_Types.opts =
                                        (uu___113_7194.FStar_Tactics_Types.opts);
                                      FStar_Tactics_Types.is_guard =
                                        (uu___113_7194.FStar_Tactics_Types.is_guard)
                                    })]))))))
  
let (trefl : Prims.unit tac) =
  bind cur_goal
    (fun g  ->
       let uu____7214 =
         FStar_Syntax_Util.un_squash g.FStar_Tactics_Types.goal_ty  in
       match uu____7214 with
       | FStar_Pervasives_Native.Some t ->
           let uu____7226 = FStar_Syntax_Util.head_and_args' t  in
           (match uu____7226 with
            | (hd1,args) ->
                let uu____7259 =
                  let uu____7272 =
                    let uu____7273 = FStar_Syntax_Util.un_uinst hd1  in
                    uu____7273.FStar_Syntax_Syntax.n  in
                  (uu____7272, args)  in
                (match uu____7259 with
                 | (FStar_Syntax_Syntax.Tm_fvar
                    fv,uu____7287::(l,uu____7289)::(r,uu____7291)::[]) when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.eq2_lid
                     ->
                     let uu____7338 =
                       do_unify g.FStar_Tactics_Types.context l r  in
                     bind uu____7338
                       (fun b  ->
                          if Prims.op_Negation b
                          then
                            let uu____7347 =
                              tts g.FStar_Tactics_Types.context l  in
                            let uu____7348 =
                              tts g.FStar_Tactics_Types.context r  in
                            fail2 "trefl: not a trivial equality (%s vs %s)"
                              uu____7347 uu____7348
                          else solve g FStar_Syntax_Util.exp_unit)
                 | (hd2,uu____7351) ->
                     let uu____7368 = tts g.FStar_Tactics_Types.context t  in
                     fail1 "trefl: not an equality (%s)" uu____7368))
       | FStar_Pervasives_Native.None  -> fail "not an irrelevant goal")
  
let (dup : Prims.unit tac) =
  bind cur_goal
    (fun g  ->
       let uu____7378 =
         new_uvar "dup" g.FStar_Tactics_Types.context
           g.FStar_Tactics_Types.goal_ty
          in
       bind uu____7378
         (fun u  ->
            let g' =
              let uu___114_7385 = g  in
              {
                FStar_Tactics_Types.context =
                  (uu___114_7385.FStar_Tactics_Types.context);
                FStar_Tactics_Types.witness = u;
                FStar_Tactics_Types.goal_ty =
                  (uu___114_7385.FStar_Tactics_Types.goal_ty);
                FStar_Tactics_Types.opts =
                  (uu___114_7385.FStar_Tactics_Types.opts);
                FStar_Tactics_Types.is_guard =
                  (uu___114_7385.FStar_Tactics_Types.is_guard)
              }  in
            bind dismiss
              (fun uu____7388  ->
                 let uu____7389 =
                   let uu____7392 =
                     let uu____7393 =
                       FStar_TypeChecker_TcTerm.universe_of
                         g.FStar_Tactics_Types.context
                         g.FStar_Tactics_Types.goal_ty
                        in
                     FStar_Syntax_Util.mk_eq2 uu____7393
                       g.FStar_Tactics_Types.goal_ty u
                       g.FStar_Tactics_Types.witness
                      in
                   add_irrelevant_goal "dup equation"
                     g.FStar_Tactics_Types.context uu____7392
                     g.FStar_Tactics_Types.opts
                    in
                 bind uu____7389
                   (fun uu____7396  ->
                      let uu____7397 = add_goals [g']  in
                      bind uu____7397 (fun uu____7401  -> ret ())))))
  
let (flip : Prims.unit tac) =
  bind get
    (fun ps  ->
       match ps.FStar_Tactics_Types.goals with
       | g1::g2::gs ->
           set
             (let uu___115_7420 = ps  in
              {
                FStar_Tactics_Types.main_context =
                  (uu___115_7420.FStar_Tactics_Types.main_context);
                FStar_Tactics_Types.main_goal =
                  (uu___115_7420.FStar_Tactics_Types.main_goal);
                FStar_Tactics_Types.all_implicits =
                  (uu___115_7420.FStar_Tactics_Types.all_implicits);
                FStar_Tactics_Types.goals = (g2 :: g1 :: gs);
                FStar_Tactics_Types.smt_goals =
                  (uu___115_7420.FStar_Tactics_Types.smt_goals);
                FStar_Tactics_Types.depth =
                  (uu___115_7420.FStar_Tactics_Types.depth);
                FStar_Tactics_Types.__dump =
                  (uu___115_7420.FStar_Tactics_Types.__dump);
                FStar_Tactics_Types.psc =
                  (uu___115_7420.FStar_Tactics_Types.psc);
                FStar_Tactics_Types.entry_range =
                  (uu___115_7420.FStar_Tactics_Types.entry_range);
                FStar_Tactics_Types.guard_policy =
                  (uu___115_7420.FStar_Tactics_Types.guard_policy)
              })
       | uu____7421 -> fail "flip: less than 2 goals")
  
let (later : Prims.unit tac) =
  bind get
    (fun ps  ->
       match ps.FStar_Tactics_Types.goals with
       | [] -> ret ()
       | g::gs ->
           set
             (let uu___116_7438 = ps  in
              {
                FStar_Tactics_Types.main_context =
                  (uu___116_7438.FStar_Tactics_Types.main_context);
                FStar_Tactics_Types.main_goal =
                  (uu___116_7438.FStar_Tactics_Types.main_goal);
                FStar_Tactics_Types.all_implicits =
                  (uu___116_7438.FStar_Tactics_Types.all_implicits);
                FStar_Tactics_Types.goals = (FStar_List.append gs [g]);
                FStar_Tactics_Types.smt_goals =
                  (uu___116_7438.FStar_Tactics_Types.smt_goals);
                FStar_Tactics_Types.depth =
                  (uu___116_7438.FStar_Tactics_Types.depth);
                FStar_Tactics_Types.__dump =
                  (uu___116_7438.FStar_Tactics_Types.__dump);
                FStar_Tactics_Types.psc =
                  (uu___116_7438.FStar_Tactics_Types.psc);
                FStar_Tactics_Types.entry_range =
                  (uu___116_7438.FStar_Tactics_Types.entry_range);
                FStar_Tactics_Types.guard_policy =
                  (uu___116_7438.FStar_Tactics_Types.guard_policy)
              }))
  
let (qed : Prims.unit tac) =
  bind get
    (fun ps  ->
       match ps.FStar_Tactics_Types.goals with
       | [] -> ret ()
       | uu____7447 -> fail "Not done!")
  
let (cases :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 tac)
  =
  fun t  ->
    let uu____7465 =
      bind cur_goal
        (fun g  ->
           let uu____7479 = __tc g.FStar_Tactics_Types.context t  in
           bind uu____7479
             (fun uu____7515  ->
                match uu____7515 with
                | (t1,typ,guard) ->
                    let uu____7531 = FStar_Syntax_Util.head_and_args typ  in
                    (match uu____7531 with
                     | (hd1,args) ->
                         let uu____7574 =
                           let uu____7587 =
                             let uu____7588 = FStar_Syntax_Util.un_uinst hd1
                                in
                             uu____7588.FStar_Syntax_Syntax.n  in
                           (uu____7587, args)  in
                         (match uu____7574 with
                          | (FStar_Syntax_Syntax.Tm_fvar
                             fv,(p,uu____7607)::(q,uu____7609)::[]) when
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
                                let uu___117_7647 = g  in
                                let uu____7648 =
                                  FStar_TypeChecker_Env.push_bv
                                    g.FStar_Tactics_Types.context v_p
                                   in
                                {
                                  FStar_Tactics_Types.context = uu____7648;
                                  FStar_Tactics_Types.witness =
                                    (uu___117_7647.FStar_Tactics_Types.witness);
                                  FStar_Tactics_Types.goal_ty =
                                    (uu___117_7647.FStar_Tactics_Types.goal_ty);
                                  FStar_Tactics_Types.opts =
                                    (uu___117_7647.FStar_Tactics_Types.opts);
                                  FStar_Tactics_Types.is_guard =
                                    (uu___117_7647.FStar_Tactics_Types.is_guard)
                                }  in
                              let g2 =
                                let uu___118_7650 = g  in
                                let uu____7651 =
                                  FStar_TypeChecker_Env.push_bv
                                    g.FStar_Tactics_Types.context v_q
                                   in
                                {
                                  FStar_Tactics_Types.context = uu____7651;
                                  FStar_Tactics_Types.witness =
                                    (uu___118_7650.FStar_Tactics_Types.witness);
                                  FStar_Tactics_Types.goal_ty =
                                    (uu___118_7650.FStar_Tactics_Types.goal_ty);
                                  FStar_Tactics_Types.opts =
                                    (uu___118_7650.FStar_Tactics_Types.opts);
                                  FStar_Tactics_Types.is_guard =
                                    (uu___118_7650.FStar_Tactics_Types.is_guard)
                                }  in
                              bind dismiss
                                (fun uu____7658  ->
                                   let uu____7659 = add_goals [g1; g2]  in
                                   bind uu____7659
                                     (fun uu____7668  ->
                                        let uu____7669 =
                                          let uu____7674 =
                                            FStar_Syntax_Syntax.bv_to_name
                                              v_p
                                             in
                                          let uu____7675 =
                                            FStar_Syntax_Syntax.bv_to_name
                                              v_q
                                             in
                                          (uu____7674, uu____7675)  in
                                        ret uu____7669))
                          | uu____7680 ->
                              let uu____7693 =
                                tts g.FStar_Tactics_Types.context typ  in
                              fail1 "Not a disjunction: %s" uu____7693))))
       in
    FStar_All.pipe_left (wrap_err "cases") uu____7465
  
let (set_options : Prims.string -> Prims.unit tac) =
  fun s  ->
    bind cur_goal
      (fun g  ->
         FStar_Options.push ();
         (let uu____7731 = FStar_Util.smap_copy g.FStar_Tactics_Types.opts
             in
          FStar_Options.set uu____7731);
         (let res = FStar_Options.set_options FStar_Options.Set s  in
          let opts' = FStar_Options.peek ()  in
          FStar_Options.pop ();
          (match res with
           | FStar_Getopt.Success  ->
               let g' =
                 let uu___119_7738 = g  in
                 {
                   FStar_Tactics_Types.context =
                     (uu___119_7738.FStar_Tactics_Types.context);
                   FStar_Tactics_Types.witness =
                     (uu___119_7738.FStar_Tactics_Types.witness);
                   FStar_Tactics_Types.goal_ty =
                     (uu___119_7738.FStar_Tactics_Types.goal_ty);
                   FStar_Tactics_Types.opts = opts';
                   FStar_Tactics_Types.is_guard =
                     (uu___119_7738.FStar_Tactics_Types.is_guard)
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
  FStar_Syntax_Syntax.typ ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac)
  =
  fun ty  ->
    fun tm  ->
      let uu____7782 =
        bind cur_goal
          (fun goal  ->
             let env =
               FStar_TypeChecker_Env.set_expected_typ
                 goal.FStar_Tactics_Types.context ty
                in
             let uu____7790 = __tc env tm  in
             bind uu____7790
               (fun uu____7810  ->
                  match uu____7810 with
                  | (tm1,typ,guard) ->
                      let uu____7822 =
                        proc_guard "unquote" env guard
                          goal.FStar_Tactics_Types.opts
                         in
                      bind uu____7822 (fun uu____7826  -> ret tm1)))
         in
      FStar_All.pipe_left (wrap_err "unquote") uu____7782
  
let (uvar_env :
  env ->
    FStar_Syntax_Syntax.typ FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.term tac)
  =
  fun env  ->
    fun ty  ->
      let uu____7845 =
        match ty with
        | FStar_Pervasives_Native.Some ty1 -> ret ty1
        | FStar_Pervasives_Native.None  ->
            let uu____7851 =
              let uu____7852 = FStar_Syntax_Util.type_u ()  in
              FStar_All.pipe_left FStar_Pervasives_Native.fst uu____7852  in
            new_uvar "uvar_env.2" env uu____7851
         in
      bind uu____7845
        (fun typ  ->
           let uu____7864 = new_uvar "uvar_env" env typ  in
           bind uu____7864 (fun t  -> ret t))
  
let (unshelve : FStar_Syntax_Syntax.term -> Prims.unit tac) =
  fun t  ->
    let uu____7876 =
      bind get
        (fun ps  ->
           let env = ps.FStar_Tactics_Types.main_context  in
           let opts =
             match ps.FStar_Tactics_Types.goals with
             | g::uu____7887 -> g.FStar_Tactics_Types.opts
             | uu____7890 -> FStar_Options.peek ()  in
           let uu____7893 = __tc env t  in
           bind uu____7893
             (fun uu____7913  ->
                match uu____7913 with
                | (t1,typ,guard) ->
                    let uu____7925 = proc_guard "unshelve" env guard opts  in
                    bind uu____7925
                      (fun uu____7930  ->
                         let uu____7931 =
                           let uu____7934 =
                             let uu____7935 = bnorm env t1  in
                             let uu____7936 = bnorm env typ  in
                             {
                               FStar_Tactics_Types.context = env;
                               FStar_Tactics_Types.witness = uu____7935;
                               FStar_Tactics_Types.goal_ty = uu____7936;
                               FStar_Tactics_Types.opts = opts;
                               FStar_Tactics_Types.is_guard = false
                             }  in
                           [uu____7934]  in
                         add_goals uu____7931)))
       in
    FStar_All.pipe_left (wrap_err "unshelve") uu____7876
  
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
          (fun uu____7969  ->
             let uu____7970 = FStar_Options.unsafe_tactic_exec ()  in
             if uu____7970
             then
               let s =
                 FStar_Util.launch_process true "tactic_launch" prog args
                   input (fun uu____7976  -> fun uu____7977  -> false)
                  in
               ret s
             else
               fail
                 "launch_process: will not run anything unless --unsafe_tactic_exec is provided")
  
let (fresh_bv_named :
  Prims.string -> FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.bv tac) =
  fun nm  ->
    fun t  ->
      bind idtac
        (fun uu____7991  ->
           let uu____7992 =
             FStar_Syntax_Syntax.gen_bv nm FStar_Pervasives_Native.None t  in
           ret uu____7992)
  
let (change : FStar_Syntax_Syntax.typ -> Prims.unit tac) =
  fun ty  ->
    let uu____8000 =
      mlog
        (fun uu____8005  ->
           let uu____8006 = FStar_Syntax_Print.term_to_string ty  in
           FStar_Util.print1 "change: ty = %s\n" uu____8006)
        (fun uu____8008  ->
           bind cur_goal
             (fun g  ->
                let uu____8012 = __tc g.FStar_Tactics_Types.context ty  in
                bind uu____8012
                  (fun uu____8032  ->
                     match uu____8032 with
                     | (ty1,uu____8042,guard) ->
                         let uu____8044 =
                           proc_guard "change" g.FStar_Tactics_Types.context
                             guard g.FStar_Tactics_Types.opts
                            in
                         bind uu____8044
                           (fun uu____8049  ->
                              let uu____8050 =
                                do_unify g.FStar_Tactics_Types.context
                                  g.FStar_Tactics_Types.goal_ty ty1
                                 in
                              bind uu____8050
                                (fun bb  ->
                                   if bb
                                   then
                                     replace_cur
                                       (let uu___120_8059 = g  in
                                        {
                                          FStar_Tactics_Types.context =
                                            (uu___120_8059.FStar_Tactics_Types.context);
                                          FStar_Tactics_Types.witness =
                                            (uu___120_8059.FStar_Tactics_Types.witness);
                                          FStar_Tactics_Types.goal_ty = ty1;
                                          FStar_Tactics_Types.opts =
                                            (uu___120_8059.FStar_Tactics_Types.opts);
                                          FStar_Tactics_Types.is_guard =
                                            (uu___120_8059.FStar_Tactics_Types.is_guard)
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
                                      let uu____8066 =
                                        do_unify
                                          g.FStar_Tactics_Types.context ng
                                          nty
                                         in
                                      bind uu____8066
                                        (fun b  ->
                                           if b
                                           then
                                             replace_cur
                                               (let uu___121_8075 = g  in
                                                {
                                                  FStar_Tactics_Types.context
                                                    =
                                                    (uu___121_8075.FStar_Tactics_Types.context);
                                                  FStar_Tactics_Types.witness
                                                    =
                                                    (uu___121_8075.FStar_Tactics_Types.witness);
                                                  FStar_Tactics_Types.goal_ty
                                                    = ty1;
                                                  FStar_Tactics_Types.opts =
                                                    (uu___121_8075.FStar_Tactics_Types.opts);
                                                  FStar_Tactics_Types.is_guard
                                                    =
                                                    (uu___121_8075.FStar_Tactics_Types.is_guard)
                                                })
                                           else fail "not convertible")))))))
       in
    FStar_All.pipe_left (wrap_err "change") uu____8000
  
let (goal_of_goal_ty :
  env ->
    FStar_Syntax_Syntax.typ ->
      (FStar_Tactics_Types.goal,FStar_TypeChecker_Env.guard_t)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun typ  ->
      let uu____8095 =
        FStar_TypeChecker_Util.new_implicit_var "proofstate_of_goal_ty"
          typ.FStar_Syntax_Syntax.pos env typ
         in
      match uu____8095 with
      | (u,uu____8113,g_u) ->
          let g =
            let uu____8128 = FStar_Options.peek ()  in
            {
              FStar_Tactics_Types.context = env;
              FStar_Tactics_Types.witness = u;
              FStar_Tactics_Types.goal_ty = typ;
              FStar_Tactics_Types.opts = uu____8128;
              FStar_Tactics_Types.is_guard = false
            }  in
          (g, g_u)
  
let (proofstate_of_goal_ty :
  env ->
    FStar_Syntax_Syntax.typ ->
      (FStar_Tactics_Types.proofstate,FStar_Syntax_Syntax.term)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun typ  ->
      let uu____8139 = goal_of_goal_ty env typ  in
      match uu____8139 with
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
              FStar_Tactics_Types.guard_policy = FStar_Tactics_Types.SMT
            }  in
          (ps, (g.FStar_Tactics_Types.witness))
  