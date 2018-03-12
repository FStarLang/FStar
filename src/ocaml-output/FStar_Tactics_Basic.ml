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
  
let (apply_lemma : FStar_Syntax_Syntax.term -> Prims.unit tac) =
  fun tm  ->
    let uu____3276 =
      let uu____3279 =
        mlog
          (fun uu____3284  ->
             let uu____3285 = FStar_Syntax_Print.term_to_string tm  in
             FStar_Util.print1 "apply_lemma: tm = %s\n" uu____3285)
          (fun uu____3288  ->
             let is_unit_t t =
               let uu____3293 =
                 let uu____3294 = FStar_Syntax_Subst.compress t  in
                 uu____3294.FStar_Syntax_Syntax.n  in
               match uu____3293 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.unit_lid
                   -> true
               | uu____3298 -> false  in
             bind cur_goal
               (fun goal  ->
                  let uu____3302 = __tc goal.FStar_Tactics_Types.context tm
                     in
                  bind uu____3302
                    (fun uu____3324  ->
                       match uu____3324 with
                       | (tm1,t,guard) ->
                           let uu____3336 =
                             FStar_Syntax_Util.arrow_formals_comp t  in
                           (match uu____3336 with
                            | (bs,comp) ->
                                if
                                  Prims.op_Negation
                                    (FStar_Syntax_Util.is_lemma_comp comp)
                                then fail "not a lemma"
                                else
                                  (let uu____3366 =
                                     FStar_List.fold_left
                                       (fun uu____3412  ->
                                          fun uu____3413  ->
                                            match (uu____3412, uu____3413)
                                            with
                                            | ((uvs,guard1,subst1),(b,aq)) ->
                                                let b_t =
                                                  FStar_Syntax_Subst.subst
                                                    subst1
                                                    b.FStar_Syntax_Syntax.sort
                                                   in
                                                let uu____3516 =
                                                  is_unit_t b_t  in
                                                if uu____3516
                                                then
                                                  (((FStar_Syntax_Util.exp_unit,
                                                      aq) :: uvs), guard1,
                                                    ((FStar_Syntax_Syntax.NT
                                                        (b,
                                                          FStar_Syntax_Util.exp_unit))
                                                    :: subst1))
                                                else
                                                  (let uu____3554 =
                                                     FStar_TypeChecker_Util.new_implicit_var
                                                       "apply_lemma"
                                                       (goal.FStar_Tactics_Types.goal_ty).FStar_Syntax_Syntax.pos
                                                       goal.FStar_Tactics_Types.context
                                                       b_t
                                                      in
                                                   match uu____3554 with
                                                   | (u,uu____3584,g_u) ->
                                                       let uu____3598 =
                                                         FStar_TypeChecker_Rel.conj_guard
                                                           guard1 g_u
                                                          in
                                                       (((u, aq) :: uvs),
                                                         uu____3598,
                                                         ((FStar_Syntax_Syntax.NT
                                                             (b, u)) ::
                                                         subst1))))
                                       ([], guard, []) bs
                                      in
                                   match uu____3366 with
                                   | (uvs,implicits,subst1) ->
                                       let uvs1 = FStar_List.rev uvs  in
                                       let comp1 =
                                         FStar_Syntax_Subst.subst_comp subst1
                                           comp
                                          in
                                       let uu____3668 =
                                         let uu____3677 =
                                           let uu____3686 =
                                             FStar_Syntax_Util.comp_to_comp_typ
                                               comp1
                                              in
                                           uu____3686.FStar_Syntax_Syntax.effect_args
                                            in
                                         match uu____3677 with
                                         | pre::post::uu____3697 ->
                                             ((FStar_Pervasives_Native.fst
                                                 pre),
                                               (FStar_Pervasives_Native.fst
                                                  post))
                                         | uu____3738 ->
                                             failwith
                                               "apply_lemma: impossible: not a lemma"
                                          in
                                       (match uu____3668 with
                                        | (pre,post) ->
                                            let post1 =
                                              let uu____3770 =
                                                let uu____3779 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    FStar_Syntax_Util.exp_unit
                                                   in
                                                [uu____3779]  in
                                              FStar_Syntax_Util.mk_app post
                                                uu____3770
                                               in
                                            let uu____3780 =
                                              let uu____3783 =
                                                FStar_Syntax_Util.mk_squash
                                                  FStar_Syntax_Syntax.U_zero
                                                  post1
                                                 in
                                              do_unify
                                                goal.FStar_Tactics_Types.context
                                                uu____3783
                                                goal.FStar_Tactics_Types.goal_ty
                                               in
                                            bind uu____3780
                                              (fun b  ->
                                                 if Prims.op_Negation b
                                                 then
                                                   let uu____3791 =
                                                     tts
                                                       goal.FStar_Tactics_Types.context
                                                       tm1
                                                      in
                                                   let uu____3792 =
                                                     let uu____3793 =
                                                       FStar_Syntax_Util.mk_squash
                                                         FStar_Syntax_Syntax.U_zero
                                                         post1
                                                        in
                                                     tts
                                                       goal.FStar_Tactics_Types.context
                                                       uu____3793
                                                      in
                                                   let uu____3794 =
                                                     tts
                                                       goal.FStar_Tactics_Types.context
                                                       goal.FStar_Tactics_Types.goal_ty
                                                      in
                                                   fail3
                                                     "Cannot instantiate lemma %s (with postcondition: %s) to match goal (%s)"
                                                     uu____3791 uu____3792
                                                     uu____3794
                                                 else
                                                   (let uu____3796 =
                                                      add_implicits
                                                        implicits.FStar_TypeChecker_Env.implicits
                                                       in
                                                    bind uu____3796
                                                      (fun uu____3801  ->
                                                         let uu____3802 =
                                                           solve goal
                                                             FStar_Syntax_Util.exp_unit
                                                            in
                                                         bind uu____3802
                                                           (fun uu____3810 
                                                              ->
                                                              let is_free_uvar
                                                                uv t1 =
                                                                let free_uvars
                                                                  =
                                                                  let uu____3821
                                                                    =
                                                                    let uu____3828
                                                                    =
                                                                    FStar_Syntax_Free.uvars
                                                                    t1  in
                                                                    FStar_Util.set_elements
                                                                    uu____3828
                                                                     in
                                                                  FStar_List.map
                                                                    FStar_Pervasives_Native.fst
                                                                    uu____3821
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
                                                                let uu____3869
                                                                  =
                                                                  FStar_Syntax_Util.head_and_args
                                                                    t1
                                                                   in
                                                                match uu____3869
                                                                with
                                                                | (hd1,uu____3885)
                                                                    ->
                                                                    (
                                                                    match 
                                                                    hd1.FStar_Syntax_Syntax.n
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Tm_uvar
                                                                    (uv,uu____3907)
                                                                    ->
                                                                    appears
                                                                    uv goals
                                                                    | 
                                                                    uu____3932
                                                                    -> false)
                                                                 in
                                                              let uu____3933
                                                                =
                                                                FStar_All.pipe_right
                                                                  implicits.FStar_TypeChecker_Env.implicits
                                                                  (mapM
                                                                    (fun
                                                                    uu____4005
                                                                     ->
                                                                    match uu____4005
                                                                    with
                                                                    | 
                                                                    (_msg,env,_uvar,term,typ,uu____4033)
                                                                    ->
                                                                    let uu____4034
                                                                    =
                                                                    FStar_Syntax_Util.head_and_args
                                                                    term  in
                                                                    (match uu____4034
                                                                    with
                                                                    | 
                                                                    (hd1,uu____4060)
                                                                    ->
                                                                    let uu____4081
                                                                    =
                                                                    let uu____4082
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    hd1  in
                                                                    uu____4082.FStar_Syntax_Syntax.n
                                                                     in
                                                                    (match uu____4081
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Tm_uvar
                                                                    uu____4095
                                                                    ->
                                                                    let uu____4112
                                                                    =
                                                                    let uu____4121
                                                                    =
                                                                    let uu____4124
                                                                    =
                                                                    let uu___90_4125
                                                                    = goal
                                                                     in
                                                                    let uu____4126
                                                                    =
                                                                    bnorm
                                                                    goal.FStar_Tactics_Types.context
                                                                    term  in
                                                                    let uu____4127
                                                                    =
                                                                    bnorm
                                                                    goal.FStar_Tactics_Types.context
                                                                    typ  in
                                                                    {
                                                                    FStar_Tactics_Types.context
                                                                    =
                                                                    (uu___90_4125.FStar_Tactics_Types.context);
                                                                    FStar_Tactics_Types.witness
                                                                    =
                                                                    uu____4126;
                                                                    FStar_Tactics_Types.goal_ty
                                                                    =
                                                                    uu____4127;
                                                                    FStar_Tactics_Types.opts
                                                                    =
                                                                    (uu___90_4125.FStar_Tactics_Types.opts);
                                                                    FStar_Tactics_Types.is_guard
                                                                    =
                                                                    (uu___90_4125.FStar_Tactics_Types.is_guard)
                                                                    }  in
                                                                    [uu____4124]
                                                                     in
                                                                    (uu____4121,
                                                                    [])  in
                                                                    ret
                                                                    uu____4112
                                                                    | 
                                                                    uu____4140
                                                                    ->
                                                                    let g_typ
                                                                    =
                                                                    let uu____4142
                                                                    =
                                                                    FStar_Options.__temp_fast_implicits
                                                                    ()  in
                                                                    if
                                                                    uu____4142
                                                                    then
                                                                    FStar_TypeChecker_TcTerm.check_type_of_well_typed_term
                                                                    false env
                                                                    term typ
                                                                    else
                                                                    (let term1
                                                                    =
                                                                    bnorm env
                                                                    term  in
                                                                    let uu____4145
                                                                    =
                                                                    let uu____4152
                                                                    =
                                                                    FStar_TypeChecker_Env.set_expected_typ
                                                                    env typ
                                                                     in
                                                                    env.FStar_TypeChecker_Env.type_of
                                                                    uu____4152
                                                                    term1  in
                                                                    match uu____4145
                                                                    with
                                                                    | 
                                                                    (uu____4153,uu____4154,g_typ)
                                                                    -> g_typ)
                                                                     in
                                                                    let uu____4156
                                                                    =
                                                                    goal_from_guard
                                                                    "apply_lemma solved arg"
                                                                    goal.FStar_Tactics_Types.context
                                                                    g_typ
                                                                    goal.FStar_Tactics_Types.opts
                                                                     in
                                                                    bind
                                                                    uu____4156
                                                                    (fun
                                                                    uu___58_4172
                                                                     ->
                                                                    match uu___58_4172
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
                                                              bind uu____3933
                                                                (fun goals_ 
                                                                   ->
                                                                   let sub_goals
                                                                    =
                                                                    let uu____4240
                                                                    =
                                                                    FStar_List.map
                                                                    FStar_Pervasives_Native.fst
                                                                    goals_
                                                                     in
                                                                    FStar_List.flatten
                                                                    uu____4240
                                                                     in
                                                                   let smt_goals
                                                                    =
                                                                    let uu____4262
                                                                    =
                                                                    FStar_List.map
                                                                    FStar_Pervasives_Native.snd
                                                                    goals_
                                                                     in
                                                                    FStar_List.flatten
                                                                    uu____4262
                                                                     in
                                                                   let rec filter'
                                                                    a f xs =
                                                                    match xs
                                                                    with
                                                                    | 
                                                                    [] -> []
                                                                    | 
                                                                    x::xs1 ->
                                                                    let uu____4317
                                                                    = f x xs1
                                                                     in
                                                                    if
                                                                    uu____4317
                                                                    then
                                                                    let uu____4320
                                                                    =
                                                                    filter'
                                                                    () f xs1
                                                                     in x ::
                                                                    uu____4320
                                                                    else
                                                                    filter'
                                                                    () f xs1
                                                                     in
                                                                   let sub_goals1
                                                                    =
                                                                    Obj.magic
                                                                    (filter'
                                                                    ()
                                                                    (fun a436
                                                                     ->
                                                                    fun a437 
                                                                    ->
                                                                    (Obj.magic
                                                                    (fun g 
                                                                    ->
                                                                    fun goals
                                                                     ->
                                                                    let uu____4334
                                                                    =
                                                                    checkone
                                                                    g.FStar_Tactics_Types.witness
                                                                    goals  in
                                                                    Prims.op_Negation
                                                                    uu____4334))
                                                                    a436 a437)
                                                                    (Obj.magic
                                                                    sub_goals))
                                                                     in
                                                                   let uu____4335
                                                                    =
                                                                    proc_guard
                                                                    "apply_lemma guard"
                                                                    goal.FStar_Tactics_Types.context
                                                                    guard
                                                                    goal.FStar_Tactics_Types.opts
                                                                     in
                                                                   bind
                                                                    uu____4335
                                                                    (fun
                                                                    uu____4340
                                                                     ->
                                                                    let uu____4341
                                                                    =
                                                                    let uu____4344
                                                                    =
                                                                    let uu____4345
                                                                    =
                                                                    let uu____4346
                                                                    =
                                                                    FStar_Syntax_Util.mk_squash
                                                                    FStar_Syntax_Syntax.U_zero
                                                                    pre  in
                                                                    istrivial
                                                                    goal.FStar_Tactics_Types.context
                                                                    uu____4346
                                                                     in
                                                                    Prims.op_Negation
                                                                    uu____4345
                                                                     in
                                                                    if
                                                                    uu____4344
                                                                    then
                                                                    add_irrelevant_goal
                                                                    "apply_lemma precondition"
                                                                    goal.FStar_Tactics_Types.context
                                                                    pre
                                                                    goal.FStar_Tactics_Types.opts
                                                                    else
                                                                    ret ()
                                                                     in
                                                                    bind
                                                                    uu____4341
                                                                    (fun
                                                                    uu____4352
                                                                     ->
                                                                    let uu____4353
                                                                    =
                                                                    add_smt_goals
                                                                    smt_goals
                                                                     in
                                                                    bind
                                                                    uu____4353
                                                                    (fun
                                                                    uu____4357
                                                                     ->
                                                                    add_goals
                                                                    sub_goals1))))))))))))))
         in
      focus uu____3279  in
    FStar_All.pipe_left (wrap_err "apply_lemma") uu____3276
  
let (destruct_eq' :
  FStar_Syntax_Syntax.typ ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun typ  ->
    let uu____4377 = FStar_Syntax_Util.destruct_typ_as_formula typ  in
    match uu____4377 with
    | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn
        (l,uu____4387::(e1,uu____4389)::(e2,uu____4391)::[])) when
        FStar_Ident.lid_equals l FStar_Parser_Const.eq2_lid ->
        FStar_Pervasives_Native.Some (e1, e2)
    | uu____4450 -> FStar_Pervasives_Native.None
  
let (destruct_eq :
  FStar_Syntax_Syntax.typ ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun typ  ->
    let uu____4472 = destruct_eq' typ  in
    match uu____4472 with
    | FStar_Pervasives_Native.Some t -> FStar_Pervasives_Native.Some t
    | FStar_Pervasives_Native.None  ->
        let uu____4502 = FStar_Syntax_Util.un_squash typ  in
        (match uu____4502 with
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
        let uu____4558 = FStar_TypeChecker_Env.pop_bv e1  in
        match uu____4558 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (bv',e') ->
            if FStar_Syntax_Syntax.bv_eq bvar bv'
            then FStar_Pervasives_Native.Some (e', [])
            else
              (let uu____4606 = aux e'  in
               FStar_Util.map_opt uu____4606
                 (fun uu____4630  ->
                    match uu____4630 with | (e'',bvs) -> (e'', (bv' :: bvs))))
         in
      let uu____4651 = aux e  in
      FStar_Util.map_opt uu____4651
        (fun uu____4675  ->
           match uu____4675 with | (e',bvs) -> (e', (FStar_List.rev bvs)))
  
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
          let uu____4730 = split_env b1 g.FStar_Tactics_Types.context  in
          FStar_Util.map_opt uu____4730
            (fun uu____4754  ->
               match uu____4754 with
               | (e0,bvs) ->
                   let s1 bv =
                     let uu___91_4771 = bv  in
                     let uu____4772 =
                       FStar_Syntax_Subst.subst s bv.FStar_Syntax_Syntax.sort
                        in
                     {
                       FStar_Syntax_Syntax.ppname =
                         (uu___91_4771.FStar_Syntax_Syntax.ppname);
                       FStar_Syntax_Syntax.index =
                         (uu___91_4771.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort = uu____4772
                     }  in
                   let bvs1 = FStar_List.map s1 bvs  in
                   let c = push_bvs e0 (b2 :: bvs1)  in
                   let w =
                     FStar_Syntax_Subst.subst s g.FStar_Tactics_Types.witness
                      in
                   let t =
                     FStar_Syntax_Subst.subst s g.FStar_Tactics_Types.goal_ty
                      in
                   let uu___92_4781 = g  in
                   {
                     FStar_Tactics_Types.context = c;
                     FStar_Tactics_Types.witness = w;
                     FStar_Tactics_Types.goal_ty = t;
                     FStar_Tactics_Types.opts =
                       (uu___92_4781.FStar_Tactics_Types.opts);
                     FStar_Tactics_Types.is_guard =
                       (uu___92_4781.FStar_Tactics_Types.is_guard)
                   })
  
let (rewrite : FStar_Syntax_Syntax.binder -> Prims.unit tac) =
  fun h  ->
    bind cur_goal
      (fun goal  ->
         let uu____4794 = h  in
         match uu____4794 with
         | (bv,uu____4798) ->
             mlog
               (fun uu____4802  ->
                  let uu____4803 = FStar_Syntax_Print.bv_to_string bv  in
                  let uu____4804 =
                    tts goal.FStar_Tactics_Types.context
                      bv.FStar_Syntax_Syntax.sort
                     in
                  FStar_Util.print2 "+++Rewrite %s : %s\n" uu____4803
                    uu____4804)
               (fun uu____4807  ->
                  let uu____4808 =
                    split_env bv goal.FStar_Tactics_Types.context  in
                  match uu____4808 with
                  | FStar_Pervasives_Native.None  ->
                      fail "rewrite: binder not found in environment"
                  | FStar_Pervasives_Native.Some (e0,bvs) ->
                      let uu____4837 =
                        destruct_eq bv.FStar_Syntax_Syntax.sort  in
                      (match uu____4837 with
                       | FStar_Pervasives_Native.Some (x,e) ->
                           let uu____4852 =
                             let uu____4853 = FStar_Syntax_Subst.compress x
                                in
                             uu____4853.FStar_Syntax_Syntax.n  in
                           (match uu____4852 with
                            | FStar_Syntax_Syntax.Tm_name x1 ->
                                let s = [FStar_Syntax_Syntax.NT (x1, e)]  in
                                let s1 bv1 =
                                  let uu___93_4866 = bv1  in
                                  let uu____4867 =
                                    FStar_Syntax_Subst.subst s
                                      bv1.FStar_Syntax_Syntax.sort
                                     in
                                  {
                                    FStar_Syntax_Syntax.ppname =
                                      (uu___93_4866.FStar_Syntax_Syntax.ppname);
                                    FStar_Syntax_Syntax.index =
                                      (uu___93_4866.FStar_Syntax_Syntax.index);
                                    FStar_Syntax_Syntax.sort = uu____4867
                                  }  in
                                let bvs1 = FStar_List.map s1 bvs  in
                                let uu____4873 =
                                  let uu___94_4874 = goal  in
                                  let uu____4875 = push_bvs e0 (bv :: bvs1)
                                     in
                                  let uu____4876 =
                                    FStar_Syntax_Subst.subst s
                                      goal.FStar_Tactics_Types.witness
                                     in
                                  let uu____4877 =
                                    FStar_Syntax_Subst.subst s
                                      goal.FStar_Tactics_Types.goal_ty
                                     in
                                  {
                                    FStar_Tactics_Types.context = uu____4875;
                                    FStar_Tactics_Types.witness = uu____4876;
                                    FStar_Tactics_Types.goal_ty = uu____4877;
                                    FStar_Tactics_Types.opts =
                                      (uu___94_4874.FStar_Tactics_Types.opts);
                                    FStar_Tactics_Types.is_guard =
                                      (uu___94_4874.FStar_Tactics_Types.is_guard)
                                  }  in
                                replace_cur uu____4873
                            | uu____4878 ->
                                fail
                                  "rewrite: Not an equality hypothesis with a variable on the LHS")
                       | uu____4879 ->
                           fail "rewrite: Not an equality hypothesis")))
  
let (rename_to :
  FStar_Syntax_Syntax.binder -> Prims.string -> Prims.unit tac) =
  fun b  ->
    fun s  ->
      bind cur_goal
        (fun goal  ->
           let uu____4904 = b  in
           match uu____4904 with
           | (bv,uu____4908) ->
               let bv' =
                 FStar_Syntax_Syntax.freshen_bv
                   (let uu___95_4912 = bv  in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (FStar_Ident.mk_ident
                           (s,
                             ((bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange)));
                      FStar_Syntax_Syntax.index =
                        (uu___95_4912.FStar_Syntax_Syntax.index);
                      FStar_Syntax_Syntax.sort =
                        (uu___95_4912.FStar_Syntax_Syntax.sort)
                    })
                  in
               let s1 =
                 let uu____4916 =
                   let uu____4917 =
                     let uu____4924 = FStar_Syntax_Syntax.bv_to_name bv'  in
                     (bv, uu____4924)  in
                   FStar_Syntax_Syntax.NT uu____4917  in
                 [uu____4916]  in
               let uu____4925 = subst_goal bv bv' s1 goal  in
               (match uu____4925 with
                | FStar_Pervasives_Native.None  ->
                    fail "rename_to: binder not found in environment"
                | FStar_Pervasives_Native.Some goal1 -> replace_cur goal1))
  
let (binder_retype : FStar_Syntax_Syntax.binder -> Prims.unit tac) =
  fun b  ->
    bind cur_goal
      (fun goal  ->
         let uu____4944 = b  in
         match uu____4944 with
         | (bv,uu____4948) ->
             let uu____4949 = split_env bv goal.FStar_Tactics_Types.context
                in
             (match uu____4949 with
              | FStar_Pervasives_Native.None  ->
                  fail "binder_retype: binder is not present in environment"
              | FStar_Pervasives_Native.Some (e0,bvs) ->
                  let uu____4978 = FStar_Syntax_Util.type_u ()  in
                  (match uu____4978 with
                   | (ty,u) ->
                       let uu____4987 = new_uvar "binder_retype" e0 ty  in
                       bind uu____4987
                         (fun t'  ->
                            let bv'' =
                              let uu___96_4997 = bv  in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___96_4997.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___96_4997.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = t'
                              }  in
                            let s =
                              let uu____5001 =
                                let uu____5002 =
                                  let uu____5009 =
                                    FStar_Syntax_Syntax.bv_to_name bv''  in
                                  (bv, uu____5009)  in
                                FStar_Syntax_Syntax.NT uu____5002  in
                              [uu____5001]  in
                            let bvs1 =
                              FStar_List.map
                                (fun b1  ->
                                   let uu___97_5017 = b1  in
                                   let uu____5018 =
                                     FStar_Syntax_Subst.subst s
                                       b1.FStar_Syntax_Syntax.sort
                                      in
                                   {
                                     FStar_Syntax_Syntax.ppname =
                                       (uu___97_5017.FStar_Syntax_Syntax.ppname);
                                     FStar_Syntax_Syntax.index =
                                       (uu___97_5017.FStar_Syntax_Syntax.index);
                                     FStar_Syntax_Syntax.sort = uu____5018
                                   }) bvs
                               in
                            let env' = push_bvs e0 (bv'' :: bvs1)  in
                            bind dismiss
                              (fun uu____5024  ->
                                 let uu____5025 =
                                   let uu____5028 =
                                     let uu____5031 =
                                       let uu___98_5032 = goal  in
                                       let uu____5033 =
                                         FStar_Syntax_Subst.subst s
                                           goal.FStar_Tactics_Types.witness
                                          in
                                       let uu____5034 =
                                         FStar_Syntax_Subst.subst s
                                           goal.FStar_Tactics_Types.goal_ty
                                          in
                                       {
                                         FStar_Tactics_Types.context = env';
                                         FStar_Tactics_Types.witness =
                                           uu____5033;
                                         FStar_Tactics_Types.goal_ty =
                                           uu____5034;
                                         FStar_Tactics_Types.opts =
                                           (uu___98_5032.FStar_Tactics_Types.opts);
                                         FStar_Tactics_Types.is_guard =
                                           (uu___98_5032.FStar_Tactics_Types.is_guard)
                                       }  in
                                     [uu____5031]  in
                                   add_goals uu____5028  in
                                 bind uu____5025
                                   (fun uu____5037  ->
                                      let uu____5038 =
                                        FStar_Syntax_Util.mk_eq2
                                          (FStar_Syntax_Syntax.U_succ u) ty
                                          bv.FStar_Syntax_Syntax.sort t'
                                         in
                                      add_irrelevant_goal
                                        "binder_retype equation" e0
                                        uu____5038
                                        goal.FStar_Tactics_Types.opts))))))
  
let (norm_binder_type :
  FStar_Syntax_Embeddings.norm_step Prims.list ->
    FStar_Syntax_Syntax.binder -> Prims.unit tac)
  =
  fun s  ->
    fun b  ->
      bind cur_goal
        (fun goal  ->
           let uu____5059 = b  in
           match uu____5059 with
           | (bv,uu____5063) ->
               let uu____5064 = split_env bv goal.FStar_Tactics_Types.context
                  in
               (match uu____5064 with
                | FStar_Pervasives_Native.None  ->
                    fail
                      "binder_retype: binder is not present in environment"
                | FStar_Pervasives_Native.Some (e0,bvs) ->
                    let steps =
                      let uu____5096 =
                        FStar_TypeChecker_Normalize.tr_norm_steps s  in
                      FStar_List.append
                        [FStar_TypeChecker_Normalize.Reify;
                        FStar_TypeChecker_Normalize.UnfoldTac] uu____5096
                       in
                    let sort' =
                      normalize steps e0 bv.FStar_Syntax_Syntax.sort  in
                    let bv' =
                      let uu___99_5101 = bv  in
                      {
                        FStar_Syntax_Syntax.ppname =
                          (uu___99_5101.FStar_Syntax_Syntax.ppname);
                        FStar_Syntax_Syntax.index =
                          (uu___99_5101.FStar_Syntax_Syntax.index);
                        FStar_Syntax_Syntax.sort = sort'
                      }  in
                    let env' = push_bvs e0 (bv' :: bvs)  in
                    replace_cur
                      (let uu___100_5105 = goal  in
                       {
                         FStar_Tactics_Types.context = env';
                         FStar_Tactics_Types.witness =
                           (uu___100_5105.FStar_Tactics_Types.witness);
                         FStar_Tactics_Types.goal_ty =
                           (uu___100_5105.FStar_Tactics_Types.goal_ty);
                         FStar_Tactics_Types.opts =
                           (uu___100_5105.FStar_Tactics_Types.opts);
                         FStar_Tactics_Types.is_guard =
                           (uu___100_5105.FStar_Tactics_Types.is_guard)
                       })))
  
let (revert : Prims.unit tac) =
  bind cur_goal
    (fun goal  ->
       let uu____5113 =
         FStar_TypeChecker_Env.pop_bv goal.FStar_Tactics_Types.context  in
       match uu____5113 with
       | FStar_Pervasives_Native.None  -> fail "Cannot revert; empty context"
       | FStar_Pervasives_Native.Some (x,env') ->
           let typ' =
             let uu____5135 =
               FStar_Syntax_Syntax.mk_Total goal.FStar_Tactics_Types.goal_ty
                in
             FStar_Syntax_Util.arrow [(x, FStar_Pervasives_Native.None)]
               uu____5135
              in
           let w' =
             FStar_Syntax_Util.abs [(x, FStar_Pervasives_Native.None)]
               goal.FStar_Tactics_Types.witness FStar_Pervasives_Native.None
              in
           replace_cur
             (let uu___101_5169 = goal  in
              {
                FStar_Tactics_Types.context = env';
                FStar_Tactics_Types.witness = w';
                FStar_Tactics_Types.goal_ty = typ';
                FStar_Tactics_Types.opts =
                  (uu___101_5169.FStar_Tactics_Types.opts);
                FStar_Tactics_Types.is_guard =
                  (uu___101_5169.FStar_Tactics_Types.is_guard)
              }))
  
let (free_in :
  FStar_Syntax_Syntax.bv -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun bv  ->
    fun t  ->
      let uu____5176 = FStar_Syntax_Free.names t  in
      FStar_Util.set_mem bv uu____5176
  
let rec (clear : FStar_Syntax_Syntax.binder -> Prims.unit tac) =
  fun b  ->
    let bv = FStar_Pervasives_Native.fst b  in
    bind cur_goal
      (fun goal  ->
         mlog
           (fun uu____5192  ->
              let uu____5193 = FStar_Syntax_Print.binder_to_string b  in
              let uu____5194 =
                let uu____5195 =
                  let uu____5196 =
                    FStar_TypeChecker_Env.all_binders
                      goal.FStar_Tactics_Types.context
                     in
                  FStar_All.pipe_right uu____5196 FStar_List.length  in
                FStar_All.pipe_right uu____5195 FStar_Util.string_of_int  in
              FStar_Util.print2 "Clear of (%s), env has %s binders\n"
                uu____5193 uu____5194)
           (fun uu____5207  ->
              let uu____5208 = split_env bv goal.FStar_Tactics_Types.context
                 in
              match uu____5208 with
              | FStar_Pervasives_Native.None  ->
                  fail "Cannot clear; binder not in environment"
              | FStar_Pervasives_Native.Some (e',bvs) ->
                  let rec check1 bvs1 =
                    match bvs1 with
                    | [] -> ret ()
                    | bv'::bvs2 ->
                        let uu____5253 =
                          free_in bv bv'.FStar_Syntax_Syntax.sort  in
                        if uu____5253
                        then
                          let uu____5256 =
                            let uu____5257 =
                              FStar_Syntax_Print.bv_to_string bv'  in
                            FStar_Util.format1
                              "Cannot clear; binder present in the type of %s"
                              uu____5257
                             in
                          fail uu____5256
                        else check1 bvs2
                     in
                  let uu____5259 =
                    free_in bv goal.FStar_Tactics_Types.goal_ty  in
                  if uu____5259
                  then fail "Cannot clear; binder present in goal"
                  else
                    (let uu____5263 = check1 bvs  in
                     bind uu____5263
                       (fun uu____5269  ->
                          let env' = push_bvs e' bvs  in
                          let uu____5271 =
                            new_uvar "clear.witness" env'
                              goal.FStar_Tactics_Types.goal_ty
                             in
                          bind uu____5271
                            (fun ut  ->
                               let uu____5277 =
                                 do_unify goal.FStar_Tactics_Types.context
                                   goal.FStar_Tactics_Types.witness ut
                                  in
                               bind uu____5277
                                 (fun b1  ->
                                    if b1
                                    then
                                      replace_cur
                                        (let uu___102_5286 = goal  in
                                         {
                                           FStar_Tactics_Types.context = env';
                                           FStar_Tactics_Types.witness = ut;
                                           FStar_Tactics_Types.goal_ty =
                                             (uu___102_5286.FStar_Tactics_Types.goal_ty);
                                           FStar_Tactics_Types.opts =
                                             (uu___102_5286.FStar_Tactics_Types.opts);
                                           FStar_Tactics_Types.is_guard =
                                             (uu___102_5286.FStar_Tactics_Types.is_guard)
                                         })
                                    else
                                      fail
                                        "Cannot clear; binder appears in witness"))))))
  
let (clear_top : Prims.unit tac) =
  bind cur_goal
    (fun goal  ->
       let uu____5295 =
         FStar_TypeChecker_Env.pop_bv goal.FStar_Tactics_Types.context  in
       match uu____5295 with
       | FStar_Pervasives_Native.None  -> fail "Cannot clear; empty context"
       | FStar_Pervasives_Native.Some (x,uu____5309) ->
           let uu____5314 = FStar_Syntax_Syntax.mk_binder x  in
           clear uu____5314)
  
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
           let uu___103_5330 = g  in
           {
             FStar_Tactics_Types.context = ctx';
             FStar_Tactics_Types.witness =
               (uu___103_5330.FStar_Tactics_Types.witness);
             FStar_Tactics_Types.goal_ty =
               (uu___103_5330.FStar_Tactics_Types.goal_ty);
             FStar_Tactics_Types.opts =
               (uu___103_5330.FStar_Tactics_Types.opts);
             FStar_Tactics_Types.is_guard =
               (uu___103_5330.FStar_Tactics_Types.is_guard)
           }  in
         bind dismiss (fun uu____5332  -> add_goals [g']))
  
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
           let uu___104_5348 = g  in
           {
             FStar_Tactics_Types.context = ctx';
             FStar_Tactics_Types.witness =
               (uu___104_5348.FStar_Tactics_Types.witness);
             FStar_Tactics_Types.goal_ty =
               (uu___104_5348.FStar_Tactics_Types.goal_ty);
             FStar_Tactics_Types.opts =
               (uu___104_5348.FStar_Tactics_Types.opts);
             FStar_Tactics_Types.is_guard =
               (uu___104_5348.FStar_Tactics_Types.is_guard)
           }  in
         bind dismiss (fun uu____5350  -> add_goals [g']))
  
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
            let uu____5382 = FStar_Syntax_Subst.compress t  in
            uu____5382.FStar_Syntax_Syntax.n  in
          let uu____5385 =
            if d = FStar_Tactics_Types.TopDown
            then
              f env
                (let uu___108_5391 = t  in
                 {
                   FStar_Syntax_Syntax.n = tn;
                   FStar_Syntax_Syntax.pos =
                     (uu___108_5391.FStar_Syntax_Syntax.pos);
                   FStar_Syntax_Syntax.vars =
                     (uu___108_5391.FStar_Syntax_Syntax.vars)
                 })
            else ret t  in
          bind uu____5385
            (fun t1  ->
               let ff = tac_fold_env d f env  in
               let tn1 =
                 let uu____5405 =
                   let uu____5406 = FStar_Syntax_Subst.compress t1  in
                   uu____5406.FStar_Syntax_Syntax.n  in
                 match uu____5405 with
                 | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
                     let uu____5433 = ff hd1  in
                     bind uu____5433
                       (fun hd2  ->
                          let fa uu____5453 =
                            match uu____5453 with
                            | (a,q) ->
                                let uu____5466 = ff a  in
                                bind uu____5466 (fun a1  -> ret (a1, q))
                             in
                          let uu____5479 = mapM fa args  in
                          bind uu____5479
                            (fun args1  ->
                               ret (FStar_Syntax_Syntax.Tm_app (hd2, args1))))
                 | FStar_Syntax_Syntax.Tm_abs (bs,t2,k) ->
                     let uu____5539 = FStar_Syntax_Subst.open_term bs t2  in
                     (match uu____5539 with
                      | (bs1,t') ->
                          let uu____5548 =
                            let uu____5551 =
                              FStar_TypeChecker_Env.push_binders env bs1  in
                            tac_fold_env d f uu____5551 t'  in
                          bind uu____5548
                            (fun t''  ->
                               let uu____5555 =
                                 let uu____5556 =
                                   let uu____5573 =
                                     FStar_Syntax_Subst.close_binders bs1  in
                                   let uu____5574 =
                                     FStar_Syntax_Subst.close bs1 t''  in
                                   (uu____5573, uu____5574, k)  in
                                 FStar_Syntax_Syntax.Tm_abs uu____5556  in
                               ret uu____5555))
                 | FStar_Syntax_Syntax.Tm_arrow (bs,k) -> ret tn
                 | FStar_Syntax_Syntax.Tm_match (hd1,brs) ->
                     let uu____5633 = ff hd1  in
                     bind uu____5633
                       (fun hd2  ->
                          let ffb br =
                            let uu____5646 =
                              FStar_Syntax_Subst.open_branch br  in
                            match uu____5646 with
                            | (pat,w,e) ->
                                let uu____5668 = ff e  in
                                bind uu____5668
                                  (fun e1  ->
                                     let br1 =
                                       FStar_Syntax_Subst.close_branch
                                         (pat, w, e1)
                                        in
                                     ret br1)
                             in
                          let uu____5681 = mapM ffb brs  in
                          bind uu____5681
                            (fun brs1  ->
                               ret (FStar_Syntax_Syntax.Tm_match (hd2, brs1))))
                 | FStar_Syntax_Syntax.Tm_let
                     ((false
                       ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl bv;
                          FStar_Syntax_Syntax.lbunivs = uu____5695;
                          FStar_Syntax_Syntax.lbtyp = uu____5696;
                          FStar_Syntax_Syntax.lbeff = uu____5697;
                          FStar_Syntax_Syntax.lbdef = def;
                          FStar_Syntax_Syntax.lbattrs = uu____5699;
                          FStar_Syntax_Syntax.lbpos = uu____5700;_}::[]),e)
                     ->
                     let lb =
                       let uu____5725 =
                         let uu____5726 = FStar_Syntax_Subst.compress t1  in
                         uu____5726.FStar_Syntax_Syntax.n  in
                       match uu____5725 with
                       | FStar_Syntax_Syntax.Tm_let
                           ((false ,lb::[]),uu____5730) -> lb
                       | uu____5743 -> failwith "impossible"  in
                     let fflb lb1 =
                       let uu____5750 = ff lb1.FStar_Syntax_Syntax.lbdef  in
                       bind uu____5750
                         (fun def1  ->
                            ret
                              (let uu___105_5756 = lb1  in
                               {
                                 FStar_Syntax_Syntax.lbname =
                                   (uu___105_5756.FStar_Syntax_Syntax.lbname);
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___105_5756.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp =
                                   (uu___105_5756.FStar_Syntax_Syntax.lbtyp);
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___105_5756.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def1;
                                 FStar_Syntax_Syntax.lbattrs =
                                   (uu___105_5756.FStar_Syntax_Syntax.lbattrs);
                                 FStar_Syntax_Syntax.lbpos =
                                   (uu___105_5756.FStar_Syntax_Syntax.lbpos)
                               }))
                        in
                     let uu____5757 = fflb lb  in
                     bind uu____5757
                       (fun lb1  ->
                          let uu____5766 =
                            let uu____5771 =
                              let uu____5772 =
                                FStar_Syntax_Syntax.mk_binder bv  in
                              [uu____5772]  in
                            FStar_Syntax_Subst.open_term uu____5771 e  in
                          match uu____5766 with
                          | (bs,e1) ->
                              let uu____5777 = ff e1  in
                              bind uu____5777
                                (fun e2  ->
                                   let e3 = FStar_Syntax_Subst.close bs e2
                                      in
                                   ret
                                     (FStar_Syntax_Syntax.Tm_let
                                        ((false, [lb1]), e3))))
                 | FStar_Syntax_Syntax.Tm_let ((true ,lbs),e) ->
                     let fflb lb =
                       let uu____5814 = ff lb.FStar_Syntax_Syntax.lbdef  in
                       bind uu____5814
                         (fun def  ->
                            ret
                              (let uu___106_5820 = lb  in
                               {
                                 FStar_Syntax_Syntax.lbname =
                                   (uu___106_5820.FStar_Syntax_Syntax.lbname);
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___106_5820.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp =
                                   (uu___106_5820.FStar_Syntax_Syntax.lbtyp);
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___106_5820.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def;
                                 FStar_Syntax_Syntax.lbattrs =
                                   (uu___106_5820.FStar_Syntax_Syntax.lbattrs);
                                 FStar_Syntax_Syntax.lbpos =
                                   (uu___106_5820.FStar_Syntax_Syntax.lbpos)
                               }))
                        in
                     let uu____5821 = FStar_Syntax_Subst.open_let_rec lbs e
                        in
                     (match uu____5821 with
                      | (lbs1,e1) ->
                          let uu____5836 = mapM fflb lbs1  in
                          bind uu____5836
                            (fun lbs2  ->
                               let uu____5848 = ff e1  in
                               bind uu____5848
                                 (fun e2  ->
                                    let uu____5856 =
                                      FStar_Syntax_Subst.close_let_rec lbs2
                                        e2
                                       in
                                    match uu____5856 with
                                    | (lbs3,e3) ->
                                        ret
                                          (FStar_Syntax_Syntax.Tm_let
                                             ((true, lbs3), e3)))))
                 | FStar_Syntax_Syntax.Tm_ascribed (t2,asc,eff) ->
                     let uu____5922 = ff t2  in
                     bind uu____5922
                       (fun t3  ->
                          ret
                            (FStar_Syntax_Syntax.Tm_ascribed (t3, asc, eff)))
                 | FStar_Syntax_Syntax.Tm_meta (t2,m) ->
                     let uu____5951 = ff t2  in
                     bind uu____5951
                       (fun t3  -> ret (FStar_Syntax_Syntax.Tm_meta (t3, m)))
                 | uu____5956 -> ret tn  in
               bind tn1
                 (fun tn2  ->
                    let t' =
                      let uu___107_5963 = t1  in
                      {
                        FStar_Syntax_Syntax.n = tn2;
                        FStar_Syntax_Syntax.pos =
                          (uu___107_5963.FStar_Syntax_Syntax.pos);
                        FStar_Syntax_Syntax.vars =
                          (uu___107_5963.FStar_Syntax_Syntax.vars)
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
            let uu____5992 = FStar_TypeChecker_TcTerm.tc_term env t  in
            match uu____5992 with
            | (t1,lcomp,g) ->
                let uu____6004 =
                  (let uu____6007 =
                     FStar_Syntax_Util.is_pure_or_ghost_lcomp lcomp  in
                   Prims.op_Negation uu____6007) ||
                    (let uu____6009 = FStar_TypeChecker_Rel.is_trivial g  in
                     Prims.op_Negation uu____6009)
                   in
                if uu____6004
                then ret t1
                else
                  (let rewrite_eq =
                     let typ = lcomp.FStar_Syntax_Syntax.res_typ  in
                     let uu____6019 = new_uvar "pointwise_rec" env typ  in
                     bind uu____6019
                       (fun ut  ->
                          log ps
                            (fun uu____6030  ->
                               let uu____6031 =
                                 FStar_Syntax_Print.term_to_string t1  in
                               let uu____6032 =
                                 FStar_Syntax_Print.term_to_string ut  in
                               FStar_Util.print2
                                 "Pointwise_rec: making equality\n\t%s ==\n\t%s\n"
                                 uu____6031 uu____6032);
                          (let uu____6033 =
                             let uu____6036 =
                               let uu____6037 =
                                 FStar_TypeChecker_TcTerm.universe_of env typ
                                  in
                               FStar_Syntax_Util.mk_eq2 uu____6037 typ t1 ut
                                in
                             add_irrelevant_goal "pointwise_rec equation" env
                               uu____6036 opts
                              in
                           bind uu____6033
                             (fun uu____6040  ->
                                let uu____6041 =
                                  bind tau
                                    (fun uu____6047  ->
                                       let ut1 =
                                         FStar_TypeChecker_Normalize.reduce_uvar_solutions
                                           env ut
                                          in
                                       log ps
                                         (fun uu____6053  ->
                                            let uu____6054 =
                                              FStar_Syntax_Print.term_to_string
                                                t1
                                               in
                                            let uu____6055 =
                                              FStar_Syntax_Print.term_to_string
                                                ut1
                                               in
                                            FStar_Util.print2
                                              "Pointwise_rec: succeeded rewriting\n\t%s to\n\t%s\n"
                                              uu____6054 uu____6055);
                                       ret ut1)
                                   in
                                focus uu____6041)))
                      in
                   let uu____6056 = trytac' rewrite_eq  in
                   bind uu____6056
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
          let uu____6204 = FStar_Syntax_Subst.compress t  in
          maybe_continue ctrl uu____6204
            (fun t1  ->
               let uu____6208 =
                 f env
                   (let uu___111_6217 = t1  in
                    {
                      FStar_Syntax_Syntax.n = (t1.FStar_Syntax_Syntax.n);
                      FStar_Syntax_Syntax.pos =
                        (uu___111_6217.FStar_Syntax_Syntax.pos);
                      FStar_Syntax_Syntax.vars =
                        (uu___111_6217.FStar_Syntax_Syntax.vars)
                    })
                  in
               bind uu____6208
                 (fun uu____6229  ->
                    match uu____6229 with
                    | (t2,ctrl1) ->
                        maybe_continue ctrl1 t2
                          (fun t3  ->
                             let uu____6248 =
                               let uu____6249 =
                                 FStar_Syntax_Subst.compress t3  in
                               uu____6249.FStar_Syntax_Syntax.n  in
                             match uu____6248 with
                             | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
                                 let uu____6282 =
                                   ctrl_tac_fold f env ctrl1 hd1  in
                                 bind uu____6282
                                   (fun uu____6307  ->
                                      match uu____6307 with
                                      | (hd2,ctrl2) ->
                                          let ctrl3 = keep_going ctrl2  in
                                          let uu____6323 =
                                            ctrl_tac_fold_args f env ctrl3
                                              args
                                             in
                                          bind uu____6323
                                            (fun uu____6350  ->
                                               match uu____6350 with
                                               | (args1,ctrl4) ->
                                                   ret
                                                     ((let uu___109_6380 = t3
                                                          in
                                                       {
                                                         FStar_Syntax_Syntax.n
                                                           =
                                                           (FStar_Syntax_Syntax.Tm_app
                                                              (hd2, args1));
                                                         FStar_Syntax_Syntax.pos
                                                           =
                                                           (uu___109_6380.FStar_Syntax_Syntax.pos);
                                                         FStar_Syntax_Syntax.vars
                                                           =
                                                           (uu___109_6380.FStar_Syntax_Syntax.vars)
                                                       }), ctrl4)))
                             | FStar_Syntax_Syntax.Tm_abs (bs,t4,k) ->
                                 let uu____6406 =
                                   FStar_Syntax_Subst.open_term bs t4  in
                                 (match uu____6406 with
                                  | (bs1,t') ->
                                      let uu____6421 =
                                        let uu____6428 =
                                          FStar_TypeChecker_Env.push_binders
                                            env bs1
                                           in
                                        ctrl_tac_fold f uu____6428 ctrl1 t'
                                         in
                                      bind uu____6421
                                        (fun uu____6446  ->
                                           match uu____6446 with
                                           | (t'',ctrl2) ->
                                               let uu____6461 =
                                                 let uu____6468 =
                                                   let uu___110_6471 = t4  in
                                                   let uu____6474 =
                                                     let uu____6475 =
                                                       let uu____6492 =
                                                         FStar_Syntax_Subst.close_binders
                                                           bs1
                                                          in
                                                       let uu____6493 =
                                                         FStar_Syntax_Subst.close
                                                           bs1 t''
                                                          in
                                                       (uu____6492,
                                                         uu____6493, k)
                                                        in
                                                     FStar_Syntax_Syntax.Tm_abs
                                                       uu____6475
                                                      in
                                                   {
                                                     FStar_Syntax_Syntax.n =
                                                       uu____6474;
                                                     FStar_Syntax_Syntax.pos
                                                       =
                                                       (uu___110_6471.FStar_Syntax_Syntax.pos);
                                                     FStar_Syntax_Syntax.vars
                                                       =
                                                       (uu___110_6471.FStar_Syntax_Syntax.vars)
                                                   }  in
                                                 (uu____6468, ctrl2)  in
                                               ret uu____6461))
                             | FStar_Syntax_Syntax.Tm_arrow (bs,k) ->
                                 ret (t3, ctrl1)
                             | uu____6526 -> ret (t3, ctrl1))))

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
              let uu____6577 = ctrl_tac_fold f env ctrl t  in
              bind uu____6577
                (fun uu____6605  ->
                   match uu____6605 with
                   | (t1,ctrl1) ->
                       let uu____6624 = ctrl_tac_fold_args f env ctrl1 ts1
                          in
                       bind uu____6624
                         (fun uu____6655  ->
                            match uu____6655 with
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
              let uu____6739 =
                let uu____6746 =
                  add_irrelevant_goal "dummy" env FStar_Syntax_Util.t_true
                    opts
                   in
                bind uu____6746
                  (fun uu____6755  ->
                     let uu____6756 = ctrl t1  in
                     bind uu____6756
                       (fun res  -> bind trivial (fun uu____6783  -> ret res)))
                 in
              bind uu____6739
                (fun uu____6799  ->
                   match uu____6799 with
                   | (should_rewrite,ctrl1) ->
                       if Prims.op_Negation should_rewrite
                       then ret (t1, ctrl1)
                       else
                         (let uu____6823 =
                            FStar_TypeChecker_TcTerm.tc_term env t1  in
                          match uu____6823 with
                          | (t2,lcomp,g) ->
                              let uu____6839 =
                                (let uu____6842 =
                                   FStar_Syntax_Util.is_pure_or_ghost_lcomp
                                     lcomp
                                    in
                                 Prims.op_Negation uu____6842) ||
                                  (let uu____6844 =
                                     FStar_TypeChecker_Rel.is_trivial g  in
                                   Prims.op_Negation uu____6844)
                                 in
                              if uu____6839
                              then ret (t2, globalStop)
                              else
                                (let typ = lcomp.FStar_Syntax_Syntax.res_typ
                                    in
                                 let uu____6859 =
                                   new_uvar "pointwise_rec" env typ  in
                                 bind uu____6859
                                   (fun ut  ->
                                      log ps
                                        (fun uu____6874  ->
                                           let uu____6875 =
                                             FStar_Syntax_Print.term_to_string
                                               t2
                                              in
                                           let uu____6876 =
                                             FStar_Syntax_Print.term_to_string
                                               ut
                                              in
                                           FStar_Util.print2
                                             "Pointwise_rec: making equality\n\t%s ==\n\t%s\n"
                                             uu____6875 uu____6876);
                                      (let uu____6877 =
                                         let uu____6880 =
                                           let uu____6881 =
                                             FStar_TypeChecker_TcTerm.universe_of
                                               env typ
                                              in
                                           FStar_Syntax_Util.mk_eq2
                                             uu____6881 typ t2 ut
                                            in
                                         add_irrelevant_goal
                                           "rewrite_rec equation" env
                                           uu____6880 opts
                                          in
                                       bind uu____6877
                                         (fun uu____6888  ->
                                            let uu____6889 =
                                              bind rewriter
                                                (fun uu____6903  ->
                                                   let ut1 =
                                                     FStar_TypeChecker_Normalize.reduce_uvar_solutions
                                                       env ut
                                                      in
                                                   log ps
                                                     (fun uu____6909  ->
                                                        let uu____6910 =
                                                          FStar_Syntax_Print.term_to_string
                                                            t2
                                                           in
                                                        let uu____6911 =
                                                          FStar_Syntax_Print.term_to_string
                                                            ut1
                                                           in
                                                        FStar_Util.print2
                                                          "rewrite_rec: succeeded rewriting\n\t%s to\n\t%s\n"
                                                          uu____6910
                                                          uu____6911);
                                                   ret (ut1, ctrl1))
                                               in
                                            focus uu____6889))))))
  
let (topdown_rewrite :
  (FStar_Syntax_Syntax.term ->
     (Prims.bool,FStar_BigInt.t) FStar_Pervasives_Native.tuple2 tac)
    -> Prims.unit tac -> Prims.unit tac)
  =
  fun ctrl  ->
    fun rewriter  ->
      bind get
        (fun ps  ->
           let uu____6955 =
             match ps.FStar_Tactics_Types.goals with
             | g::gs -> (g, gs)
             | [] -> failwith "Pointwise: no goals"  in
           match uu____6955 with
           | (g,gs) ->
               let gt1 = g.FStar_Tactics_Types.goal_ty  in
               (log ps
                  (fun uu____6992  ->
                     let uu____6993 = FStar_Syntax_Print.term_to_string gt1
                        in
                     FStar_Util.print1 "Pointwise starting with %s\n"
                       uu____6993);
                bind dismiss_all
                  (fun uu____6996  ->
                     let uu____6997 =
                       ctrl_tac_fold
                         (rewrite_rec ps ctrl rewriter
                            g.FStar_Tactics_Types.opts)
                         g.FStar_Tactics_Types.context keepGoing gt1
                        in
                     bind uu____6997
                       (fun uu____7015  ->
                          match uu____7015 with
                          | (gt',uu____7023) ->
                              (log ps
                                 (fun uu____7027  ->
                                    let uu____7028 =
                                      FStar_Syntax_Print.term_to_string gt'
                                       in
                                    FStar_Util.print1
                                      "Pointwise seems to have succeded with %s\n"
                                      uu____7028);
                               (let uu____7029 = push_goals gs  in
                                bind uu____7029
                                  (fun uu____7033  ->
                                     add_goals
                                       [(let uu___112_7035 = g  in
                                         {
                                           FStar_Tactics_Types.context =
                                             (uu___112_7035.FStar_Tactics_Types.context);
                                           FStar_Tactics_Types.witness =
                                             (uu___112_7035.FStar_Tactics_Types.witness);
                                           FStar_Tactics_Types.goal_ty = gt';
                                           FStar_Tactics_Types.opts =
                                             (uu___112_7035.FStar_Tactics_Types.opts);
                                           FStar_Tactics_Types.is_guard =
                                             (uu___112_7035.FStar_Tactics_Types.is_guard)
                                         })])))))))
  
let (pointwise :
  FStar_Tactics_Types.direction -> Prims.unit tac -> Prims.unit tac) =
  fun d  ->
    fun tau  ->
      bind get
        (fun ps  ->
           let uu____7057 =
             match ps.FStar_Tactics_Types.goals with
             | g::gs -> (g, gs)
             | [] -> failwith "Pointwise: no goals"  in
           match uu____7057 with
           | (g,gs) ->
               let gt1 = g.FStar_Tactics_Types.goal_ty  in
               (log ps
                  (fun uu____7094  ->
                     let uu____7095 = FStar_Syntax_Print.term_to_string gt1
                        in
                     FStar_Util.print1 "Pointwise starting with %s\n"
                       uu____7095);
                bind dismiss_all
                  (fun uu____7098  ->
                     let uu____7099 =
                       tac_fold_env d
                         (pointwise_rec ps tau g.FStar_Tactics_Types.opts)
                         g.FStar_Tactics_Types.context gt1
                        in
                     bind uu____7099
                       (fun gt'  ->
                          log ps
                            (fun uu____7109  ->
                               let uu____7110 =
                                 FStar_Syntax_Print.term_to_string gt'  in
                               FStar_Util.print1
                                 "Pointwise seems to have succeded with %s\n"
                                 uu____7110);
                          (let uu____7111 = push_goals gs  in
                           bind uu____7111
                             (fun uu____7115  ->
                                add_goals
                                  [(let uu___113_7117 = g  in
                                    {
                                      FStar_Tactics_Types.context =
                                        (uu___113_7117.FStar_Tactics_Types.context);
                                      FStar_Tactics_Types.witness =
                                        (uu___113_7117.FStar_Tactics_Types.witness);
                                      FStar_Tactics_Types.goal_ty = gt';
                                      FStar_Tactics_Types.opts =
                                        (uu___113_7117.FStar_Tactics_Types.opts);
                                      FStar_Tactics_Types.is_guard =
                                        (uu___113_7117.FStar_Tactics_Types.is_guard)
                                    })]))))))
  
let (trefl : Prims.unit tac) =
  bind cur_goal
    (fun g  ->
       let uu____7137 =
         FStar_Syntax_Util.un_squash g.FStar_Tactics_Types.goal_ty  in
       match uu____7137 with
       | FStar_Pervasives_Native.Some t ->
           let uu____7149 = FStar_Syntax_Util.head_and_args' t  in
           (match uu____7149 with
            | (hd1,args) ->
                let uu____7182 =
                  let uu____7195 =
                    let uu____7196 = FStar_Syntax_Util.un_uinst hd1  in
                    uu____7196.FStar_Syntax_Syntax.n  in
                  (uu____7195, args)  in
                (match uu____7182 with
                 | (FStar_Syntax_Syntax.Tm_fvar
                    fv,uu____7210::(l,uu____7212)::(r,uu____7214)::[]) when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.eq2_lid
                     ->
                     let uu____7261 =
                       do_unify g.FStar_Tactics_Types.context l r  in
                     bind uu____7261
                       (fun b  ->
                          if Prims.op_Negation b
                          then
                            let uu____7270 =
                              tts g.FStar_Tactics_Types.context l  in
                            let uu____7271 =
                              tts g.FStar_Tactics_Types.context r  in
                            fail2 "trefl: not a trivial equality (%s vs %s)"
                              uu____7270 uu____7271
                          else solve g FStar_Syntax_Util.exp_unit)
                 | (hd2,uu____7274) ->
                     let uu____7291 = tts g.FStar_Tactics_Types.context t  in
                     fail1 "trefl: not an equality (%s)" uu____7291))
       | FStar_Pervasives_Native.None  -> fail "not an irrelevant goal")
  
let (dup : Prims.unit tac) =
  bind cur_goal
    (fun g  ->
       let uu____7301 =
         new_uvar "dup" g.FStar_Tactics_Types.context
           g.FStar_Tactics_Types.goal_ty
          in
       bind uu____7301
         (fun u  ->
            let g' =
              let uu___114_7308 = g  in
              {
                FStar_Tactics_Types.context =
                  (uu___114_7308.FStar_Tactics_Types.context);
                FStar_Tactics_Types.witness = u;
                FStar_Tactics_Types.goal_ty =
                  (uu___114_7308.FStar_Tactics_Types.goal_ty);
                FStar_Tactics_Types.opts =
                  (uu___114_7308.FStar_Tactics_Types.opts);
                FStar_Tactics_Types.is_guard =
                  (uu___114_7308.FStar_Tactics_Types.is_guard)
              }  in
            bind dismiss
              (fun uu____7311  ->
                 let uu____7312 =
                   let uu____7315 =
                     let uu____7316 =
                       FStar_TypeChecker_TcTerm.universe_of
                         g.FStar_Tactics_Types.context
                         g.FStar_Tactics_Types.goal_ty
                        in
                     FStar_Syntax_Util.mk_eq2 uu____7316
                       g.FStar_Tactics_Types.goal_ty u
                       g.FStar_Tactics_Types.witness
                      in
                   add_irrelevant_goal "dup equation"
                     g.FStar_Tactics_Types.context uu____7315
                     g.FStar_Tactics_Types.opts
                    in
                 bind uu____7312
                   (fun uu____7319  ->
                      let uu____7320 = add_goals [g']  in
                      bind uu____7320 (fun uu____7324  -> ret ())))))
  
let (flip : Prims.unit tac) =
  bind get
    (fun ps  ->
       match ps.FStar_Tactics_Types.goals with
       | g1::g2::gs ->
           set
             (let uu___115_7343 = ps  in
              {
                FStar_Tactics_Types.main_context =
                  (uu___115_7343.FStar_Tactics_Types.main_context);
                FStar_Tactics_Types.main_goal =
                  (uu___115_7343.FStar_Tactics_Types.main_goal);
                FStar_Tactics_Types.all_implicits =
                  (uu___115_7343.FStar_Tactics_Types.all_implicits);
                FStar_Tactics_Types.goals = (g2 :: g1 :: gs);
                FStar_Tactics_Types.smt_goals =
                  (uu___115_7343.FStar_Tactics_Types.smt_goals);
                FStar_Tactics_Types.depth =
                  (uu___115_7343.FStar_Tactics_Types.depth);
                FStar_Tactics_Types.__dump =
                  (uu___115_7343.FStar_Tactics_Types.__dump);
                FStar_Tactics_Types.psc =
                  (uu___115_7343.FStar_Tactics_Types.psc);
                FStar_Tactics_Types.entry_range =
                  (uu___115_7343.FStar_Tactics_Types.entry_range);
                FStar_Tactics_Types.guard_policy =
                  (uu___115_7343.FStar_Tactics_Types.guard_policy)
              })
       | uu____7344 -> fail "flip: less than 2 goals")
  
let (later : Prims.unit tac) =
  bind get
    (fun ps  ->
       match ps.FStar_Tactics_Types.goals with
       | [] -> ret ()
       | g::gs ->
           set
             (let uu___116_7361 = ps  in
              {
                FStar_Tactics_Types.main_context =
                  (uu___116_7361.FStar_Tactics_Types.main_context);
                FStar_Tactics_Types.main_goal =
                  (uu___116_7361.FStar_Tactics_Types.main_goal);
                FStar_Tactics_Types.all_implicits =
                  (uu___116_7361.FStar_Tactics_Types.all_implicits);
                FStar_Tactics_Types.goals = (FStar_List.append gs [g]);
                FStar_Tactics_Types.smt_goals =
                  (uu___116_7361.FStar_Tactics_Types.smt_goals);
                FStar_Tactics_Types.depth =
                  (uu___116_7361.FStar_Tactics_Types.depth);
                FStar_Tactics_Types.__dump =
                  (uu___116_7361.FStar_Tactics_Types.__dump);
                FStar_Tactics_Types.psc =
                  (uu___116_7361.FStar_Tactics_Types.psc);
                FStar_Tactics_Types.entry_range =
                  (uu___116_7361.FStar_Tactics_Types.entry_range);
                FStar_Tactics_Types.guard_policy =
                  (uu___116_7361.FStar_Tactics_Types.guard_policy)
              }))
  
let (qed : Prims.unit tac) =
  bind get
    (fun ps  ->
       match ps.FStar_Tactics_Types.goals with
       | [] -> ret ()
       | uu____7370 -> fail "Not done!")
  
let (cases :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 tac)
  =
  fun t  ->
    let uu____7388 =
      bind cur_goal
        (fun g  ->
           let uu____7402 = __tc g.FStar_Tactics_Types.context t  in
           bind uu____7402
             (fun uu____7438  ->
                match uu____7438 with
                | (t1,typ,guard) ->
                    let uu____7454 = FStar_Syntax_Util.head_and_args typ  in
                    (match uu____7454 with
                     | (hd1,args) ->
                         let uu____7497 =
                           let uu____7510 =
                             let uu____7511 = FStar_Syntax_Util.un_uinst hd1
                                in
                             uu____7511.FStar_Syntax_Syntax.n  in
                           (uu____7510, args)  in
                         (match uu____7497 with
                          | (FStar_Syntax_Syntax.Tm_fvar
                             fv,(p,uu____7530)::(q,uu____7532)::[]) when
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
                                let uu___117_7570 = g  in
                                let uu____7571 =
                                  FStar_TypeChecker_Env.push_bv
                                    g.FStar_Tactics_Types.context v_p
                                   in
                                {
                                  FStar_Tactics_Types.context = uu____7571;
                                  FStar_Tactics_Types.witness =
                                    (uu___117_7570.FStar_Tactics_Types.witness);
                                  FStar_Tactics_Types.goal_ty =
                                    (uu___117_7570.FStar_Tactics_Types.goal_ty);
                                  FStar_Tactics_Types.opts =
                                    (uu___117_7570.FStar_Tactics_Types.opts);
                                  FStar_Tactics_Types.is_guard =
                                    (uu___117_7570.FStar_Tactics_Types.is_guard)
                                }  in
                              let g2 =
                                let uu___118_7573 = g  in
                                let uu____7574 =
                                  FStar_TypeChecker_Env.push_bv
                                    g.FStar_Tactics_Types.context v_q
                                   in
                                {
                                  FStar_Tactics_Types.context = uu____7574;
                                  FStar_Tactics_Types.witness =
                                    (uu___118_7573.FStar_Tactics_Types.witness);
                                  FStar_Tactics_Types.goal_ty =
                                    (uu___118_7573.FStar_Tactics_Types.goal_ty);
                                  FStar_Tactics_Types.opts =
                                    (uu___118_7573.FStar_Tactics_Types.opts);
                                  FStar_Tactics_Types.is_guard =
                                    (uu___118_7573.FStar_Tactics_Types.is_guard)
                                }  in
                              bind dismiss
                                (fun uu____7581  ->
                                   let uu____7582 = add_goals [g1; g2]  in
                                   bind uu____7582
                                     (fun uu____7591  ->
                                        let uu____7592 =
                                          let uu____7597 =
                                            FStar_Syntax_Syntax.bv_to_name
                                              v_p
                                             in
                                          let uu____7598 =
                                            FStar_Syntax_Syntax.bv_to_name
                                              v_q
                                             in
                                          (uu____7597, uu____7598)  in
                                        ret uu____7592))
                          | uu____7603 ->
                              let uu____7616 =
                                tts g.FStar_Tactics_Types.context typ  in
                              fail1 "Not a disjunction: %s" uu____7616))))
       in
    FStar_All.pipe_left (wrap_err "cases") uu____7388
  
let (set_options : Prims.string -> Prims.unit tac) =
  fun s  ->
    bind cur_goal
      (fun g  ->
         FStar_Options.push ();
         (let uu____7654 = FStar_Util.smap_copy g.FStar_Tactics_Types.opts
             in
          FStar_Options.set uu____7654);
         (let res = FStar_Options.set_options FStar_Options.Set s  in
          let opts' = FStar_Options.peek ()  in
          FStar_Options.pop ();
          (match res with
           | FStar_Getopt.Success  ->
               let g' =
                 let uu___119_7661 = g  in
                 {
                   FStar_Tactics_Types.context =
                     (uu___119_7661.FStar_Tactics_Types.context);
                   FStar_Tactics_Types.witness =
                     (uu___119_7661.FStar_Tactics_Types.witness);
                   FStar_Tactics_Types.goal_ty =
                     (uu___119_7661.FStar_Tactics_Types.goal_ty);
                   FStar_Tactics_Types.opts = opts';
                   FStar_Tactics_Types.is_guard =
                     (uu___119_7661.FStar_Tactics_Types.is_guard)
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
      let uu____7705 =
        bind cur_goal
          (fun goal  ->
             let env =
               FStar_TypeChecker_Env.set_expected_typ
                 goal.FStar_Tactics_Types.context ty
                in
             let uu____7713 = __tc env tm  in
             bind uu____7713
               (fun uu____7733  ->
                  match uu____7733 with
                  | (tm1,typ,guard) ->
                      let uu____7745 =
                        proc_guard "unquote" env guard
                          goal.FStar_Tactics_Types.opts
                         in
                      bind uu____7745 (fun uu____7749  -> ret tm1)))
         in
      FStar_All.pipe_left (wrap_err "unquote") uu____7705
  
let (uvar_env :
  env ->
    FStar_Syntax_Syntax.typ FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.term tac)
  =
  fun env  ->
    fun ty  ->
      let uu____7768 =
        match ty with
        | FStar_Pervasives_Native.Some ty1 -> ret ty1
        | FStar_Pervasives_Native.None  ->
            let uu____7774 =
              let uu____7775 = FStar_Syntax_Util.type_u ()  in
              FStar_All.pipe_left FStar_Pervasives_Native.fst uu____7775  in
            new_uvar "uvar_env.2" env uu____7774
         in
      bind uu____7768
        (fun typ  ->
           let uu____7787 = new_uvar "uvar_env" env typ  in
           bind uu____7787 (fun t  -> ret t))
  
let (unshelve : FStar_Syntax_Syntax.term -> Prims.unit tac) =
  fun t  ->
    let uu____7799 =
      bind get
        (fun ps  ->
           let env = ps.FStar_Tactics_Types.main_context  in
           let opts =
             match ps.FStar_Tactics_Types.goals with
             | g::uu____7810 -> g.FStar_Tactics_Types.opts
             | uu____7813 -> FStar_Options.peek ()  in
           let uu____7816 = __tc env t  in
           bind uu____7816
             (fun uu____7836  ->
                match uu____7836 with
                | (t1,typ,guard) ->
                    let uu____7848 = proc_guard "unshelve" env guard opts  in
                    bind uu____7848
                      (fun uu____7853  ->
                         let uu____7854 =
                           let uu____7857 =
                             let uu____7858 = bnorm env t1  in
                             let uu____7859 = bnorm env typ  in
                             {
                               FStar_Tactics_Types.context = env;
                               FStar_Tactics_Types.witness = uu____7858;
                               FStar_Tactics_Types.goal_ty = uu____7859;
                               FStar_Tactics_Types.opts = opts;
                               FStar_Tactics_Types.is_guard = false
                             }  in
                           [uu____7857]  in
                         add_goals uu____7854)))
       in
    FStar_All.pipe_left (wrap_err "unshelve") uu____7799
  
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
          (fun uu____7892  ->
             let uu____7893 = FStar_Options.unsafe_tactic_exec ()  in
             if uu____7893
             then
               let s =
                 FStar_Util.launch_process true "tactic_launch" prog args
                   input (fun uu____7899  -> fun uu____7900  -> false)
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
        (fun uu____7914  ->
           let uu____7915 =
             FStar_Syntax_Syntax.gen_bv nm FStar_Pervasives_Native.None t  in
           ret uu____7915)
  
let (change : FStar_Syntax_Syntax.typ -> Prims.unit tac) =
  fun ty  ->
    let uu____7923 =
      mlog
        (fun uu____7928  ->
           let uu____7929 = FStar_Syntax_Print.term_to_string ty  in
           FStar_Util.print1 "change: ty = %s\n" uu____7929)
        (fun uu____7931  ->
           bind cur_goal
             (fun g  ->
                let uu____7935 = __tc g.FStar_Tactics_Types.context ty  in
                bind uu____7935
                  (fun uu____7955  ->
                     match uu____7955 with
                     | (ty1,uu____7965,guard) ->
                         let uu____7967 =
                           proc_guard "change" g.FStar_Tactics_Types.context
                             guard g.FStar_Tactics_Types.opts
                            in
                         bind uu____7967
                           (fun uu____7972  ->
                              let uu____7973 =
                                do_unify g.FStar_Tactics_Types.context
                                  g.FStar_Tactics_Types.goal_ty ty1
                                 in
                              bind uu____7973
                                (fun bb  ->
                                   if bb
                                   then
                                     replace_cur
                                       (let uu___120_7982 = g  in
                                        {
                                          FStar_Tactics_Types.context =
                                            (uu___120_7982.FStar_Tactics_Types.context);
                                          FStar_Tactics_Types.witness =
                                            (uu___120_7982.FStar_Tactics_Types.witness);
                                          FStar_Tactics_Types.goal_ty = ty1;
                                          FStar_Tactics_Types.opts =
                                            (uu___120_7982.FStar_Tactics_Types.opts);
                                          FStar_Tactics_Types.is_guard =
                                            (uu___120_7982.FStar_Tactics_Types.is_guard)
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
                                      let uu____7989 =
                                        do_unify
                                          g.FStar_Tactics_Types.context ng
                                          nty
                                         in
                                      bind uu____7989
                                        (fun b  ->
                                           if b
                                           then
                                             replace_cur
                                               (let uu___121_7998 = g  in
                                                {
                                                  FStar_Tactics_Types.context
                                                    =
                                                    (uu___121_7998.FStar_Tactics_Types.context);
                                                  FStar_Tactics_Types.witness
                                                    =
                                                    (uu___121_7998.FStar_Tactics_Types.witness);
                                                  FStar_Tactics_Types.goal_ty
                                                    = ty1;
                                                  FStar_Tactics_Types.opts =
                                                    (uu___121_7998.FStar_Tactics_Types.opts);
                                                  FStar_Tactics_Types.is_guard
                                                    =
                                                    (uu___121_7998.FStar_Tactics_Types.is_guard)
                                                })
                                           else fail "not convertible")))))))
       in
    FStar_All.pipe_left (wrap_err "change") uu____7923
  
let (goal_of_goal_ty :
  env ->
    FStar_Syntax_Syntax.typ ->
      (FStar_Tactics_Types.goal,FStar_TypeChecker_Env.guard_t)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun typ  ->
      let uu____8018 =
        FStar_TypeChecker_Util.new_implicit_var "proofstate_of_goal_ty"
          typ.FStar_Syntax_Syntax.pos env typ
         in
      match uu____8018 with
      | (u,uu____8036,g_u) ->
          let g =
            let uu____8051 = FStar_Options.peek ()  in
            {
              FStar_Tactics_Types.context = env;
              FStar_Tactics_Types.witness = u;
              FStar_Tactics_Types.goal_ty = typ;
              FStar_Tactics_Types.opts = uu____8051;
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
      let uu____8062 = goal_of_goal_ty env typ  in
      match uu____8062 with
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
  