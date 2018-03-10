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
  
let wrap_err : 'a . Prims.string -> 'a tac -> 'a tac =
  fun pref  ->
    fun t  ->
      mk_tac
        (fun ps  ->
           let uu____908 = run t ps  in
           match uu____908 with
           | FStar_Tactics_Result.Success (a,q) ->
               FStar_Tactics_Result.Success (a, q)
           | FStar_Tactics_Result.Failed (msg,q) ->
               FStar_Tactics_Result.Failed
                 ((Prims.strcat pref (Prims.strcat ": " msg)), q))
  
let (set : FStar_Tactics_Types.proofstate -> Prims.unit tac) =
  fun p  -> mk_tac (fun uu____925  -> FStar_Tactics_Result.Success ((), p)) 
let (do_unify :
  env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool tac)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let debug_on uu____942 =
          let uu____943 =
            FStar_Options.set_options FStar_Options.Set
              "--debug_level Rel --debug_level RelCheck"
             in
          ()  in
        let debug_off uu____947 =
          let uu____948 = FStar_Options.set_options FStar_Options.Reset ""
             in
          ()  in
        (let uu____950 =
           FStar_TypeChecker_Env.debug env (FStar_Options.Other "1346")  in
         if uu____950
         then
           (debug_on ();
            (let uu____952 = FStar_Syntax_Print.term_to_string t1  in
             let uu____953 = FStar_Syntax_Print.term_to_string t2  in
             FStar_Util.print2 "%%%%%%%%do_unify %s =? %s\n" uu____952
               uu____953))
         else ());
        (try
           let res = FStar_TypeChecker_Rel.teq_nosmt env t1 t2  in
           debug_off (); ret res
         with
         | FStar_Errors.Err (uu____972,msg) ->
             (debug_off ();
              mlog
                (fun uu____976  ->
                   FStar_Util.print1 ">> do_unify error, (%s)\n" msg)
                (fun uu____978  -> ret false))
         | FStar_Errors.Error (uu____979,msg,r) ->
             (debug_off ();
              mlog
                (fun uu____985  ->
                   let uu____986 = FStar_Range.string_of_range r  in
                   FStar_Util.print2 ">> do_unify error, (%s) at (%s)\n" msg
                     uu____986) (fun uu____988  -> ret false)))
  
let (trysolve :
  FStar_Tactics_Types.goal -> FStar_Syntax_Syntax.term -> Prims.bool tac) =
  fun goal  ->
    fun solution  ->
      do_unify goal.FStar_Tactics_Types.context solution
        goal.FStar_Tactics_Types.witness
  
let (dismiss : Prims.unit tac) =
  bind get
    (fun p  ->
       let uu____1004 =
         let uu___61_1005 = p  in
         let uu____1006 = FStar_List.tl p.FStar_Tactics_Types.goals  in
         {
           FStar_Tactics_Types.main_context =
             (uu___61_1005.FStar_Tactics_Types.main_context);
           FStar_Tactics_Types.main_goal =
             (uu___61_1005.FStar_Tactics_Types.main_goal);
           FStar_Tactics_Types.all_implicits =
             (uu___61_1005.FStar_Tactics_Types.all_implicits);
           FStar_Tactics_Types.goals = uu____1006;
           FStar_Tactics_Types.smt_goals =
             (uu___61_1005.FStar_Tactics_Types.smt_goals);
           FStar_Tactics_Types.depth =
             (uu___61_1005.FStar_Tactics_Types.depth);
           FStar_Tactics_Types.__dump =
             (uu___61_1005.FStar_Tactics_Types.__dump);
           FStar_Tactics_Types.psc = (uu___61_1005.FStar_Tactics_Types.psc);
           FStar_Tactics_Types.entry_range =
             (uu___61_1005.FStar_Tactics_Types.entry_range);
           FStar_Tactics_Types.guard_policy =
             (uu___61_1005.FStar_Tactics_Types.guard_policy)
         }  in
       set uu____1004)
  
let (solve :
  FStar_Tactics_Types.goal -> FStar_Syntax_Syntax.term -> Prims.unit tac) =
  fun goal  ->
    fun solution  ->
      let uu____1019 = trysolve goal solution  in
      bind uu____1019
        (fun b  ->
           if b
           then dismiss
           else
             (let uu____1027 =
                let uu____1028 =
                  tts goal.FStar_Tactics_Types.context solution  in
                let uu____1029 =
                  tts goal.FStar_Tactics_Types.context
                    goal.FStar_Tactics_Types.witness
                   in
                let uu____1030 =
                  tts goal.FStar_Tactics_Types.context
                    goal.FStar_Tactics_Types.goal_ty
                   in
                FStar_Util.format3 "%s does not solve %s : %s" uu____1028
                  uu____1029 uu____1030
                 in
              fail uu____1027))
  
let (dismiss_all : Prims.unit tac) =
  bind get
    (fun p  ->
       set
         (let uu___62_1037 = p  in
          {
            FStar_Tactics_Types.main_context =
              (uu___62_1037.FStar_Tactics_Types.main_context);
            FStar_Tactics_Types.main_goal =
              (uu___62_1037.FStar_Tactics_Types.main_goal);
            FStar_Tactics_Types.all_implicits =
              (uu___62_1037.FStar_Tactics_Types.all_implicits);
            FStar_Tactics_Types.goals = [];
            FStar_Tactics_Types.smt_goals =
              (uu___62_1037.FStar_Tactics_Types.smt_goals);
            FStar_Tactics_Types.depth =
              (uu___62_1037.FStar_Tactics_Types.depth);
            FStar_Tactics_Types.__dump =
              (uu___62_1037.FStar_Tactics_Types.__dump);
            FStar_Tactics_Types.psc = (uu___62_1037.FStar_Tactics_Types.psc);
            FStar_Tactics_Types.entry_range =
              (uu___62_1037.FStar_Tactics_Types.entry_range);
            FStar_Tactics_Types.guard_policy =
              (uu___62_1037.FStar_Tactics_Types.guard_policy)
          }))
  
let (nwarn : Prims.int FStar_ST.ref) =
  FStar_Util.mk_ref (Prims.parse_int "0") 
let (check_valid_goal : FStar_Tactics_Types.goal -> Prims.unit) =
  fun g  ->
    let uu____1054 = FStar_Options.defensive ()  in
    if uu____1054
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
        let uu____1066 = FStar_TypeChecker_Env.pop_bv e  in
        match uu____1066 with
        | FStar_Pervasives_Native.None  -> b3
        | FStar_Pervasives_Native.Some (bv,e1) ->
            let b4 =
              b3 &&
                (FStar_TypeChecker_Env.closed e1 bv.FStar_Syntax_Syntax.sort)
               in
            aux b4 e1
         in
      let uu____1084 =
        (let uu____1087 = aux b2 env  in Prims.op_Negation uu____1087) &&
          (let uu____1089 = FStar_ST.op_Bang nwarn  in
           uu____1089 < (Prims.parse_int "5"))
         in
      (if uu____1084
       then
         ((let uu____1110 =
             let uu____1115 =
               let uu____1116 = goal_to_string g  in
               FStar_Util.format1
                 "The following goal is ill-formed. Keeping calm and carrying on...\n<%s>\n\n"
                 uu____1116
                in
             (FStar_Errors.Warning_IllFormedGoal, uu____1115)  in
           FStar_Errors.log_issue
             (g.FStar_Tactics_Types.goal_ty).FStar_Syntax_Syntax.pos
             uu____1110);
          (let uu____1117 =
             let uu____1118 = FStar_ST.op_Bang nwarn  in
             uu____1118 + (Prims.parse_int "1")  in
           FStar_ST.op_Colon_Equals nwarn uu____1117))
       else ())
    else ()
  
let (add_goals : FStar_Tactics_Types.goal Prims.list -> Prims.unit tac) =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___63_1176 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___63_1176.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___63_1176.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___63_1176.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (FStar_List.append gs p.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___63_1176.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___63_1176.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___63_1176.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___63_1176.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___63_1176.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___63_1176.FStar_Tactics_Types.guard_policy)
            }))
  
let (add_smt_goals : FStar_Tactics_Types.goal Prims.list -> Prims.unit tac) =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___64_1194 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___64_1194.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___64_1194.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___64_1194.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___64_1194.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (FStar_List.append gs p.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___64_1194.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___64_1194.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___64_1194.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___64_1194.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___64_1194.FStar_Tactics_Types.guard_policy)
            }))
  
let (push_goals : FStar_Tactics_Types.goal Prims.list -> Prims.unit tac) =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___65_1212 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___65_1212.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___65_1212.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___65_1212.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (FStar_List.append p.FStar_Tactics_Types.goals gs);
              FStar_Tactics_Types.smt_goals =
                (uu___65_1212.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___65_1212.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___65_1212.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___65_1212.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___65_1212.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___65_1212.FStar_Tactics_Types.guard_policy)
            }))
  
let (push_smt_goals : FStar_Tactics_Types.goal Prims.list -> Prims.unit tac)
  =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___66_1230 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___66_1230.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___66_1230.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___66_1230.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___66_1230.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (FStar_List.append p.FStar_Tactics_Types.smt_goals gs);
              FStar_Tactics_Types.depth =
                (uu___66_1230.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___66_1230.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___66_1230.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___66_1230.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___66_1230.FStar_Tactics_Types.guard_policy)
            }))
  
let (replace_cur : FStar_Tactics_Types.goal -> Prims.unit tac) =
  fun g  -> bind dismiss (fun uu____1239  -> add_goals [g]) 
let (add_implicits : implicits -> Prims.unit tac) =
  fun i  ->
    bind get
      (fun p  ->
         set
           (let uu___67_1251 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___67_1251.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___67_1251.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (FStar_List.append i p.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___67_1251.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___67_1251.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___67_1251.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___67_1251.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___67_1251.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___67_1251.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___67_1251.FStar_Tactics_Types.guard_policy)
            }))
  
let (new_uvar :
  Prims.string ->
    env -> FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.term tac)
  =
  fun reason  ->
    fun env  ->
      fun typ  ->
        let uu____1277 =
          FStar_TypeChecker_Util.new_implicit_var reason
            typ.FStar_Syntax_Syntax.pos env typ
           in
        match uu____1277 with
        | (u,uu____1293,g_u) ->
            let uu____1307 =
              add_implicits g_u.FStar_TypeChecker_Env.implicits  in
            bind uu____1307 (fun uu____1311  -> ret u)
  
let (is_true : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____1315 = FStar_Syntax_Util.un_squash t  in
    match uu____1315 with
    | FStar_Pervasives_Native.Some t' ->
        let uu____1325 =
          let uu____1326 = FStar_Syntax_Subst.compress t'  in
          uu____1326.FStar_Syntax_Syntax.n  in
        (match uu____1325 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.true_lid
         | uu____1330 -> false)
    | uu____1331 -> false
  
let (is_false : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____1339 = FStar_Syntax_Util.un_squash t  in
    match uu____1339 with
    | FStar_Pervasives_Native.Some t' ->
        let uu____1349 =
          let uu____1350 = FStar_Syntax_Subst.compress t'  in
          uu____1350.FStar_Syntax_Syntax.n  in
        (match uu____1349 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.false_lid
         | uu____1354 -> false)
    | uu____1355 -> false
  
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
            let uu____1395 = env.FStar_TypeChecker_Env.universe_of env phi
               in
            FStar_Syntax_Util.mk_squash uu____1395 phi  in
          let uu____1396 = new_uvar reason env typ  in
          bind uu____1396
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
             let uu____1452 =
               (ps.FStar_Tactics_Types.main_context).FStar_TypeChecker_Env.type_of
                 e t
                in
             ret uu____1452
           with
           | ex ->
               let uu____1479 = tts e t  in
               let uu____1480 =
                 let uu____1481 = FStar_TypeChecker_Env.all_binders e  in
                 FStar_All.pipe_right uu____1481
                   (FStar_Syntax_Print.binders_to_string ", ")
                  in
               fail2 "Cannot type %s in context (%s)" uu____1479 uu____1480)
  
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
           (let uu___70_1515 = ps  in
            {
              FStar_Tactics_Types.main_context =
                (uu___70_1515.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___70_1515.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___70_1515.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___70_1515.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___70_1515.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___70_1515.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___70_1515.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___70_1515.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___70_1515.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy = pol
            }))
  
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
          let uu____1532 =
            let uu____1533 = FStar_TypeChecker_Rel.simplify_guard e g  in
            uu____1533.FStar_TypeChecker_Env.guard_f  in
          match uu____1532 with
          | FStar_TypeChecker_Common.Trivial  -> ret ()
          | FStar_TypeChecker_Common.NonTrivial f ->
              let uu____1537 = istrivial e f  in
              if uu____1537
              then ret ()
              else
                bind get
                  (fun ps  ->
                     match ps.FStar_Tactics_Types.guard_policy with
                     | FStar_Tactics_Types.Drop  -> ret ()
                     | FStar_Tactics_Types.Goal  ->
                         let uu____1545 = mk_irrelevant_goal reason e f opts
                            in
                         bind uu____1545
                           (fun goal  ->
                              let goal1 =
                                let uu___71_1552 = goal  in
                                {
                                  FStar_Tactics_Types.context =
                                    (uu___71_1552.FStar_Tactics_Types.context);
                                  FStar_Tactics_Types.witness =
                                    (uu___71_1552.FStar_Tactics_Types.witness);
                                  FStar_Tactics_Types.goal_ty =
                                    (uu___71_1552.FStar_Tactics_Types.goal_ty);
                                  FStar_Tactics_Types.opts =
                                    (uu___71_1552.FStar_Tactics_Types.opts);
                                  FStar_Tactics_Types.is_guard = true
                                }  in
                              push_goals [goal1])
                     | FStar_Tactics_Types.SMT  ->
                         let uu____1553 = mk_irrelevant_goal reason e f opts
                            in
                         bind uu____1553
                           (fun goal  ->
                              let goal1 =
                                let uu___72_1560 = goal  in
                                {
                                  FStar_Tactics_Types.context =
                                    (uu___72_1560.FStar_Tactics_Types.context);
                                  FStar_Tactics_Types.witness =
                                    (uu___72_1560.FStar_Tactics_Types.witness);
                                  FStar_Tactics_Types.goal_ty =
                                    (uu___72_1560.FStar_Tactics_Types.goal_ty);
                                  FStar_Tactics_Types.opts =
                                    (uu___72_1560.FStar_Tactics_Types.opts);
                                  FStar_Tactics_Types.is_guard = true
                                }  in
                              push_smt_goals [goal1])
                     | FStar_Tactics_Types.Force  ->
                         (try
                            let uu____1568 =
                              let uu____1569 =
                                let uu____1570 =
                                  FStar_TypeChecker_Rel.discharge_guard_no_smt
                                    e g
                                   in
                                FStar_All.pipe_left
                                  FStar_TypeChecker_Rel.is_trivial uu____1570
                                 in
                              Prims.op_Negation uu____1569  in
                            if uu____1568
                            then
                              mlog
                                (fun uu____1575  ->
                                   let uu____1576 =
                                     FStar_TypeChecker_Rel.guard_to_string e
                                       g
                                      in
                                   FStar_Util.print1 "guard = %s\n"
                                     uu____1576)
                                (fun uu____1578  ->
                                   fail1 "Forcing the guard failed %s)"
                                     reason)
                            else ret ()
                          with
                          | uu____1585 ->
                              mlog
                                (fun uu____1588  ->
                                   let uu____1589 =
                                     FStar_TypeChecker_Rel.guard_to_string e
                                       g
                                      in
                                   FStar_Util.print1 "guard = %s\n"
                                     uu____1589)
                                (fun uu____1591  ->
                                   fail1 "Forcing the guard failed (%s)"
                                     reason)))
  
let (tc : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.typ tac) =
  fun t  ->
    let uu____1599 =
      bind cur_goal
        (fun goal  ->
           let uu____1605 = __tc goal.FStar_Tactics_Types.context t  in
           bind uu____1605
             (fun uu____1625  ->
                match uu____1625 with
                | (t1,typ,guard) ->
                    let uu____1637 =
                      proc_guard "tc" goal.FStar_Tactics_Types.context guard
                        goal.FStar_Tactics_Types.opts
                       in
                    bind uu____1637 (fun uu____1641  -> ret typ)))
       in
    FStar_All.pipe_left (wrap_err "tc") uu____1599
  
let (add_irrelevant_goal :
  Prims.string ->
    env ->
      FStar_Syntax_Syntax.typ -> FStar_Options.optionstate -> Prims.unit tac)
  =
  fun reason  ->
    fun env  ->
      fun phi  ->
        fun opts  ->
          let uu____1662 = mk_irrelevant_goal reason env phi opts  in
          bind uu____1662 (fun goal  -> add_goals [goal])
  
let (trivial : Prims.unit tac) =
  bind cur_goal
    (fun goal  ->
       let uu____1674 =
         istrivial goal.FStar_Tactics_Types.context
           goal.FStar_Tactics_Types.goal_ty
          in
       if uu____1674
       then solve goal FStar_Syntax_Util.exp_unit
       else
         (let uu____1678 =
            tts goal.FStar_Tactics_Types.context
              goal.FStar_Tactics_Types.goal_ty
             in
          fail1 "Not a trivial goal: %s" uu____1678))
  
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
          let uu____1699 =
            let uu____1700 = FStar_TypeChecker_Rel.simplify_guard e g  in
            uu____1700.FStar_TypeChecker_Env.guard_f  in
          match uu____1699 with
          | FStar_TypeChecker_Common.Trivial  ->
              ret FStar_Pervasives_Native.None
          | FStar_TypeChecker_Common.NonTrivial f ->
              let uu____1708 = istrivial e f  in
              if uu____1708
              then ret FStar_Pervasives_Native.None
              else
                (let uu____1716 = mk_irrelevant_goal reason e f opts  in
                 bind uu____1716
                   (fun goal  ->
                      ret
                        (FStar_Pervasives_Native.Some
                           (let uu___75_1726 = goal  in
                            {
                              FStar_Tactics_Types.context =
                                (uu___75_1726.FStar_Tactics_Types.context);
                              FStar_Tactics_Types.witness =
                                (uu___75_1726.FStar_Tactics_Types.witness);
                              FStar_Tactics_Types.goal_ty =
                                (uu___75_1726.FStar_Tactics_Types.goal_ty);
                              FStar_Tactics_Types.opts =
                                (uu___75_1726.FStar_Tactics_Types.opts);
                              FStar_Tactics_Types.is_guard = true
                            }))))
  
let (smt : Prims.unit tac) =
  bind cur_goal
    (fun g  ->
       let uu____1734 = is_irrelevant g  in
       if uu____1734
       then bind dismiss (fun uu____1738  -> add_smt_goals [g])
       else
         (let uu____1740 =
            tts g.FStar_Tactics_Types.context g.FStar_Tactics_Types.goal_ty
             in
          fail1 "goal is not irrelevant: cannot dispatch to smt (%s)"
            uu____1740))
  
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
             let uu____1781 =
               try
                 let uu____1815 =
                   let uu____1824 = FStar_BigInt.to_int_fs n1  in
                   FStar_List.splitAt uu____1824 p.FStar_Tactics_Types.goals
                    in
                 ret uu____1815
               with | uu____1846 -> fail "divide: not enough goals"  in
             bind uu____1781
               (fun uu____1873  ->
                  match uu____1873 with
                  | (lgs,rgs) ->
                      let lp =
                        let uu___76_1899 = p  in
                        {
                          FStar_Tactics_Types.main_context =
                            (uu___76_1899.FStar_Tactics_Types.main_context);
                          FStar_Tactics_Types.main_goal =
                            (uu___76_1899.FStar_Tactics_Types.main_goal);
                          FStar_Tactics_Types.all_implicits =
                            (uu___76_1899.FStar_Tactics_Types.all_implicits);
                          FStar_Tactics_Types.goals = lgs;
                          FStar_Tactics_Types.smt_goals = [];
                          FStar_Tactics_Types.depth =
                            (uu___76_1899.FStar_Tactics_Types.depth);
                          FStar_Tactics_Types.__dump =
                            (uu___76_1899.FStar_Tactics_Types.__dump);
                          FStar_Tactics_Types.psc =
                            (uu___76_1899.FStar_Tactics_Types.psc);
                          FStar_Tactics_Types.entry_range =
                            (uu___76_1899.FStar_Tactics_Types.entry_range);
                          FStar_Tactics_Types.guard_policy =
                            (uu___76_1899.FStar_Tactics_Types.guard_policy)
                        }  in
                      let rp =
                        let uu___77_1901 = p  in
                        {
                          FStar_Tactics_Types.main_context =
                            (uu___77_1901.FStar_Tactics_Types.main_context);
                          FStar_Tactics_Types.main_goal =
                            (uu___77_1901.FStar_Tactics_Types.main_goal);
                          FStar_Tactics_Types.all_implicits =
                            (uu___77_1901.FStar_Tactics_Types.all_implicits);
                          FStar_Tactics_Types.goals = rgs;
                          FStar_Tactics_Types.smt_goals = [];
                          FStar_Tactics_Types.depth =
                            (uu___77_1901.FStar_Tactics_Types.depth);
                          FStar_Tactics_Types.__dump =
                            (uu___77_1901.FStar_Tactics_Types.__dump);
                          FStar_Tactics_Types.psc =
                            (uu___77_1901.FStar_Tactics_Types.psc);
                          FStar_Tactics_Types.entry_range =
                            (uu___77_1901.FStar_Tactics_Types.entry_range);
                          FStar_Tactics_Types.guard_policy =
                            (uu___77_1901.FStar_Tactics_Types.guard_policy)
                        }  in
                      let uu____1902 = set lp  in
                      bind uu____1902
                        (fun uu____1910  ->
                           bind l
                             (fun a  ->
                                bind get
                                  (fun lp'  ->
                                     let uu____1924 = set rp  in
                                     bind uu____1924
                                       (fun uu____1932  ->
                                          bind r
                                            (fun b  ->
                                               bind get
                                                 (fun rp'  ->
                                                    let p' =
                                                      let uu___78_1948 = p
                                                         in
                                                      {
                                                        FStar_Tactics_Types.main_context
                                                          =
                                                          (uu___78_1948.FStar_Tactics_Types.main_context);
                                                        FStar_Tactics_Types.main_goal
                                                          =
                                                          (uu___78_1948.FStar_Tactics_Types.main_goal);
                                                        FStar_Tactics_Types.all_implicits
                                                          =
                                                          (uu___78_1948.FStar_Tactics_Types.all_implicits);
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
                                                          (uu___78_1948.FStar_Tactics_Types.depth);
                                                        FStar_Tactics_Types.__dump
                                                          =
                                                          (uu___78_1948.FStar_Tactics_Types.__dump);
                                                        FStar_Tactics_Types.psc
                                                          =
                                                          (uu___78_1948.FStar_Tactics_Types.psc);
                                                        FStar_Tactics_Types.entry_range
                                                          =
                                                          (uu___78_1948.FStar_Tactics_Types.entry_range);
                                                        FStar_Tactics_Types.guard_policy
                                                          =
                                                          (uu___78_1948.FStar_Tactics_Types.guard_policy)
                                                      }  in
                                                    let uu____1949 = set p'
                                                       in
                                                    bind uu____1949
                                                      (fun uu____1957  ->
                                                         ret (a, b))))))))))
  
let focus : 'a . 'a tac -> 'a tac =
  fun f  ->
    let uu____1975 = divide FStar_BigInt.one f idtac  in
    bind uu____1975
      (fun uu____1988  -> match uu____1988 with | (a,()) -> ret a)
  
let rec map : 'a . 'a tac -> 'a Prims.list tac =
  fun tau  ->
    bind get
      (fun p  ->
         match p.FStar_Tactics_Types.goals with
         | [] -> ret []
         | uu____2022::uu____2023 ->
             let uu____2026 =
               let uu____2035 = map tau  in
               divide FStar_BigInt.one tau uu____2035  in
             bind uu____2026
               (fun uu____2053  ->
                  match uu____2053 with | (h,t) -> ret (h :: t)))
  
let (seq : Prims.unit tac -> Prims.unit tac -> Prims.unit tac) =
  fun t1  ->
    fun t2  ->
      let uu____2090 =
        bind t1
          (fun uu____2095  ->
             let uu____2096 = map t2  in
             bind uu____2096 (fun uu____2104  -> ret ()))
         in
      focus uu____2090
  
let (intro : FStar_Syntax_Syntax.binder tac) =
  let uu____2111 =
    bind cur_goal
      (fun goal  ->
         let uu____2120 =
           FStar_Syntax_Util.arrow_one goal.FStar_Tactics_Types.goal_ty  in
         match uu____2120 with
         | FStar_Pervasives_Native.Some (b,c) ->
             let uu____2135 =
               let uu____2136 = FStar_Syntax_Util.is_total_comp c  in
               Prims.op_Negation uu____2136  in
             if uu____2135
             then fail "Codomain is effectful"
             else
               (let env' =
                  FStar_TypeChecker_Env.push_binders
                    goal.FStar_Tactics_Types.context [b]
                   in
                let typ' = comp_to_typ c  in
                let uu____2142 = new_uvar "intro" env' typ'  in
                bind uu____2142
                  (fun u  ->
                     let uu____2148 =
                       let uu____2151 =
                         FStar_Syntax_Util.abs [b] u
                           FStar_Pervasives_Native.None
                          in
                       trysolve goal uu____2151  in
                     bind uu____2148
                       (fun bb  ->
                          if bb
                          then
                            let uu____2157 =
                              let uu____2160 =
                                let uu___81_2161 = goal  in
                                let uu____2162 = bnorm env' u  in
                                let uu____2163 = bnorm env' typ'  in
                                {
                                  FStar_Tactics_Types.context = env';
                                  FStar_Tactics_Types.witness = uu____2162;
                                  FStar_Tactics_Types.goal_ty = uu____2163;
                                  FStar_Tactics_Types.opts =
                                    (uu___81_2161.FStar_Tactics_Types.opts);
                                  FStar_Tactics_Types.is_guard =
                                    (uu___81_2161.FStar_Tactics_Types.is_guard)
                                }  in
                              replace_cur uu____2160  in
                            bind uu____2157 (fun uu____2165  -> ret b)
                          else fail "unification failed")))
         | FStar_Pervasives_Native.None  ->
             let uu____2171 =
               tts goal.FStar_Tactics_Types.context
                 goal.FStar_Tactics_Types.goal_ty
                in
             fail1 "goal is not an arrow (%s)" uu____2171)
     in
  FStar_All.pipe_left (wrap_err "intro") uu____2111 
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
       (let uu____2202 =
          FStar_Syntax_Util.arrow_one goal.FStar_Tactics_Types.goal_ty  in
        match uu____2202 with
        | FStar_Pervasives_Native.Some (b,c) ->
            let uu____2221 =
              let uu____2222 = FStar_Syntax_Util.is_total_comp c  in
              Prims.op_Negation uu____2222  in
            if uu____2221
            then fail "Codomain is effectful"
            else
              (let bv =
                 FStar_Syntax_Syntax.gen_bv "__recf"
                   FStar_Pervasives_Native.None
                   goal.FStar_Tactics_Types.goal_ty
                  in
               let bs =
                 let uu____2238 = FStar_Syntax_Syntax.mk_binder bv  in
                 [uu____2238; b]  in
               let env' =
                 FStar_TypeChecker_Env.push_binders
                   goal.FStar_Tactics_Types.context bs
                  in
               let uu____2240 =
                 let uu____2243 = comp_to_typ c  in
                 new_uvar "intro_rec" env' uu____2243  in
               bind uu____2240
                 (fun u  ->
                    let lb =
                      let uu____2258 =
                        FStar_Syntax_Util.abs [b] u
                          FStar_Pervasives_Native.None
                         in
                      FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl bv) []
                        goal.FStar_Tactics_Types.goal_ty
                        FStar_Parser_Const.effect_Tot_lid uu____2258 []
                        FStar_Range.dummyRange
                       in
                    let body = FStar_Syntax_Syntax.bv_to_name bv  in
                    let uu____2264 =
                      FStar_Syntax_Subst.close_let_rec [lb] body  in
                    match uu____2264 with
                    | (lbs,body1) ->
                        let tm =
                          FStar_Syntax_Syntax.mk
                            (FStar_Syntax_Syntax.Tm_let ((true, lbs), body1))
                            FStar_Pervasives_Native.None
                            (goal.FStar_Tactics_Types.witness).FStar_Syntax_Syntax.pos
                           in
                        let uu____2294 = trysolve goal tm  in
                        bind uu____2294
                          (fun bb  ->
                             if bb
                             then
                               let uu____2310 =
                                 let uu____2313 =
                                   let uu___82_2314 = goal  in
                                   let uu____2315 = bnorm env' u  in
                                   let uu____2316 =
                                     let uu____2317 = comp_to_typ c  in
                                     bnorm env' uu____2317  in
                                   {
                                     FStar_Tactics_Types.context = env';
                                     FStar_Tactics_Types.witness = uu____2315;
                                     FStar_Tactics_Types.goal_ty = uu____2316;
                                     FStar_Tactics_Types.opts =
                                       (uu___82_2314.FStar_Tactics_Types.opts);
                                     FStar_Tactics_Types.is_guard =
                                       (uu___82_2314.FStar_Tactics_Types.is_guard)
                                   }  in
                                 replace_cur uu____2313  in
                               bind uu____2310
                                 (fun uu____2324  ->
                                    let uu____2325 =
                                      let uu____2330 =
                                        FStar_Syntax_Syntax.mk_binder bv  in
                                      (uu____2330, b)  in
                                    ret uu____2325)
                             else fail "intro_rec: unification failed")))
        | FStar_Pervasives_Native.None  ->
            let uu____2344 =
              tts goal.FStar_Tactics_Types.context
                goal.FStar_Tactics_Types.goal_ty
               in
            fail1 "intro_rec: goal is not an arrow (%s)" uu____2344))
  
let (norm : FStar_Syntax_Embeddings.norm_step Prims.list -> Prims.unit tac) =
  fun s  ->
    bind cur_goal
      (fun goal  ->
         mlog
           (fun uu____2364  ->
              let uu____2365 =
                FStar_Syntax_Print.term_to_string
                  goal.FStar_Tactics_Types.witness
                 in
              FStar_Util.print1 "norm: witness = %s\n" uu____2365)
           (fun uu____2370  ->
              let steps =
                let uu____2374 = FStar_TypeChecker_Normalize.tr_norm_steps s
                   in
                FStar_List.append
                  [FStar_TypeChecker_Normalize.Reify;
                  FStar_TypeChecker_Normalize.UnfoldTac] uu____2374
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
                (let uu___83_2381 = goal  in
                 {
                   FStar_Tactics_Types.context =
                     (uu___83_2381.FStar_Tactics_Types.context);
                   FStar_Tactics_Types.witness = w;
                   FStar_Tactics_Types.goal_ty = t;
                   FStar_Tactics_Types.opts =
                     (uu___83_2381.FStar_Tactics_Types.opts);
                   FStar_Tactics_Types.is_guard =
                     (uu___83_2381.FStar_Tactics_Types.is_guard)
                 })))
  
let (norm_term_env :
  env ->
    FStar_Syntax_Embeddings.norm_step Prims.list ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac)
  =
  fun e  ->
    fun s  ->
      fun t  ->
        let uu____2399 =
          mlog
            (fun uu____2404  ->
               let uu____2405 = FStar_Syntax_Print.term_to_string t  in
               FStar_Util.print1 "norm_term: tm = %s\n" uu____2405)
            (fun uu____2407  ->
               bind get
                 (fun ps  ->
                    mlog
                      (fun uu____2412  ->
                         let uu____2413 =
                           tts ps.FStar_Tactics_Types.main_context t  in
                         FStar_Util.print1 "norm_term_env: t = %s\n"
                           uu____2413)
                      (fun uu____2416  ->
                         let uu____2417 = __tc e t  in
                         bind uu____2417
                           (fun uu____2439  ->
                              match uu____2439 with
                              | (t1,uu____2449,guard) ->
                                  (FStar_TypeChecker_Rel.force_trivial_guard
                                     e guard;
                                   (let steps =
                                      let uu____2455 =
                                        FStar_TypeChecker_Normalize.tr_norm_steps
                                          s
                                         in
                                      FStar_List.append
                                        [FStar_TypeChecker_Normalize.Reify;
                                        FStar_TypeChecker_Normalize.UnfoldTac]
                                        uu____2455
                                       in
                                    let t2 =
                                      normalize steps
                                        ps.FStar_Tactics_Types.main_context
                                        t1
                                       in
                                    ret t2))))))
           in
        FStar_All.pipe_left (wrap_err "norm_term") uu____2399
  
let (refine_intro : Prims.unit tac) =
  let uu____2467 =
    bind cur_goal
      (fun g  ->
         let uu____2474 =
           FStar_TypeChecker_Rel.base_and_refinement
             g.FStar_Tactics_Types.context g.FStar_Tactics_Types.goal_ty
            in
         match uu____2474 with
         | (uu____2487,FStar_Pervasives_Native.None ) ->
             fail "not a refinement"
         | (t,FStar_Pervasives_Native.Some (bv,phi)) ->
             let g1 =
               let uu___84_2512 = g  in
               {
                 FStar_Tactics_Types.context =
                   (uu___84_2512.FStar_Tactics_Types.context);
                 FStar_Tactics_Types.witness =
                   (uu___84_2512.FStar_Tactics_Types.witness);
                 FStar_Tactics_Types.goal_ty = t;
                 FStar_Tactics_Types.opts =
                   (uu___84_2512.FStar_Tactics_Types.opts);
                 FStar_Tactics_Types.is_guard =
                   (uu___84_2512.FStar_Tactics_Types.is_guard)
               }  in
             let uu____2513 =
               let uu____2518 =
                 let uu____2523 =
                   let uu____2524 = FStar_Syntax_Syntax.mk_binder bv  in
                   [uu____2524]  in
                 FStar_Syntax_Subst.open_term uu____2523 phi  in
               match uu____2518 with
               | (bvs,phi1) ->
                   let uu____2531 =
                     let uu____2532 = FStar_List.hd bvs  in
                     FStar_Pervasives_Native.fst uu____2532  in
                   (uu____2531, phi1)
                in
             (match uu____2513 with
              | (bv1,phi1) ->
                  let uu____2545 =
                    let uu____2548 =
                      FStar_Syntax_Subst.subst
                        [FStar_Syntax_Syntax.NT
                           (bv1, (g.FStar_Tactics_Types.witness))] phi1
                       in
                    mk_irrelevant_goal "refine_intro refinement"
                      g.FStar_Tactics_Types.context uu____2548
                      g.FStar_Tactics_Types.opts
                     in
                  bind uu____2545
                    (fun g2  ->
                       bind dismiss (fun uu____2552  -> add_goals [g1; g2]))))
     in
  FStar_All.pipe_left (wrap_err "refine_intro") uu____2467 
let (__exact_now :
  Prims.bool -> Prims.bool -> FStar_Syntax_Syntax.term -> Prims.unit tac) =
  fun set_expected_typ1  ->
    fun force_guard  ->
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
             let uu____2576 = __tc env t  in
             bind uu____2576
               (fun uu____2596  ->
                  match uu____2596 with
                  | (t1,typ,guard) ->
                      let uu____2608 =
                        if force_guard
                        then
                          proc_guard "__exact"
                            goal.FStar_Tactics_Types.context guard
                            goal.FStar_Tactics_Types.opts
                        else
                          proc_guard "__exact typing"
                            goal.FStar_Tactics_Types.context guard
                            goal.FStar_Tactics_Types.opts
                         in
                      bind uu____2608
                        (fun uu____2615  ->
                           mlog
                             (fun uu____2619  ->
                                let uu____2620 =
                                  tts goal.FStar_Tactics_Types.context typ
                                   in
                                let uu____2621 =
                                  tts goal.FStar_Tactics_Types.context
                                    goal.FStar_Tactics_Types.goal_ty
                                   in
                                FStar_Util.print2
                                  "exact: unifying %s and %s\n" uu____2620
                                  uu____2621)
                             (fun uu____2624  ->
                                let uu____2625 =
                                  do_unify goal.FStar_Tactics_Types.context
                                    typ goal.FStar_Tactics_Types.goal_ty
                                   in
                                bind uu____2625
                                  (fun b  ->
                                     if b
                                     then solve goal t1
                                     else
                                       (let uu____2633 =
                                          tts
                                            goal.FStar_Tactics_Types.context
                                            t1
                                           in
                                        let uu____2634 =
                                          tts
                                            goal.FStar_Tactics_Types.context
                                            typ
                                           in
                                        let uu____2635 =
                                          tts
                                            goal.FStar_Tactics_Types.context
                                            goal.FStar_Tactics_Types.goal_ty
                                           in
                                        let uu____2636 =
                                          tts
                                            goal.FStar_Tactics_Types.context
                                            goal.FStar_Tactics_Types.witness
                                           in
                                        fail4
                                          "%s : %s does not exactly solve the goal %s (witness = %s)"
                                          uu____2633 uu____2634 uu____2635
                                          uu____2636))))))
  
let (t_exact :
  Prims.bool -> Prims.bool -> FStar_Syntax_Syntax.term -> Prims.unit tac) =
  fun set_expected_typ1  ->
    fun force_guard  ->
      fun tm  ->
        let uu____2650 =
          mlog
            (fun uu____2655  ->
               let uu____2656 = FStar_Syntax_Print.term_to_string tm  in
               FStar_Util.print1 "t_exact: tm = %s\n" uu____2656)
            (fun uu____2659  ->
               let uu____2660 =
                 let uu____2667 =
                   __exact_now set_expected_typ1 force_guard tm  in
                 trytac' uu____2667  in
               bind uu____2660
                 (fun uu___56_2676  ->
                    match uu___56_2676 with
                    | FStar_Util.Inr r -> ret ()
                    | FStar_Util.Inl e ->
                        let uu____2685 =
                          let uu____2692 =
                            let uu____2695 =
                              norm [FStar_Syntax_Embeddings.Delta]  in
                            bind uu____2695
                              (fun uu____2699  ->
                                 bind refine_intro
                                   (fun uu____2701  ->
                                      __exact_now set_expected_typ1
                                        force_guard tm))
                             in
                          trytac' uu____2692  in
                        bind uu____2685
                          (fun uu___55_2708  ->
                             match uu___55_2708 with
                             | FStar_Util.Inr r -> ret ()
                             | FStar_Util.Inl uu____2716 -> fail e)))
           in
        FStar_All.pipe_left (wrap_err "exact") uu____2650
  
let (uvar_free_in_goal :
  FStar_Syntax_Syntax.uvar -> FStar_Tactics_Types.goal -> Prims.bool) =
  fun u  ->
    fun g  ->
      if g.FStar_Tactics_Types.is_guard
      then false
      else
        (let free_uvars =
           let uu____2731 =
             let uu____2738 =
               FStar_Syntax_Free.uvars g.FStar_Tactics_Types.goal_ty  in
             FStar_Util.set_elements uu____2738  in
           FStar_List.map FStar_Pervasives_Native.fst uu____2731  in
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
          let uu____2798 = f x  in
          bind uu____2798
            (fun y  ->
               let uu____2806 = mapM f xs  in
               bind uu____2806 (fun ys  -> ret (y :: ys)))
  
exception NoUnif 
let (uu___is_NoUnif : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with | NoUnif  -> true | uu____2824 -> false
  
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
               (fun uu____2842  ->
                  let uu____2843 = FStar_Syntax_Print.term_to_string tm  in
                  FStar_Util.print1 ">>> Calling __exact(%s)\n" uu____2843)
               (fun uu____2846  ->
                  let uu____2847 =
                    let uu____2852 = t_exact false true tm  in
                    trytac uu____2852  in
                  bind uu____2847
                    (fun uu___57_2859  ->
                       match uu___57_2859 with
                       | FStar_Pervasives_Native.Some r -> ret ()
                       | FStar_Pervasives_Native.None  ->
                           mlog
                             (fun uu____2867  ->
                                let uu____2868 =
                                  FStar_Syntax_Print.term_to_string typ  in
                                FStar_Util.print1 ">>> typ = %s\n" uu____2868)
                             (fun uu____2871  ->
                                let uu____2872 =
                                  FStar_Syntax_Util.arrow_one typ  in
                                match uu____2872 with
                                | FStar_Pervasives_Native.None  ->
                                    FStar_Exn.raise NoUnif
                                | FStar_Pervasives_Native.Some ((bv,aq),c) ->
                                    mlog
                                      (fun uu____2904  ->
                                         let uu____2905 =
                                           FStar_Syntax_Print.binder_to_string
                                             (bv, aq)
                                            in
                                         FStar_Util.print1
                                           "__apply: pushing binder %s\n"
                                           uu____2905)
                                      (fun uu____2908  ->
                                         let uu____2909 =
                                           let uu____2910 =
                                             FStar_Syntax_Util.is_total_comp
                                               c
                                              in
                                           Prims.op_Negation uu____2910  in
                                         if uu____2909
                                         then
                                           fail "apply: not total codomain"
                                         else
                                           (let uu____2914 =
                                              new_uvar "apply"
                                                goal.FStar_Tactics_Types.context
                                                bv.FStar_Syntax_Syntax.sort
                                               in
                                            bind uu____2914
                                              (fun u  ->
                                                 let tm' =
                                                   FStar_Syntax_Syntax.mk_Tm_app
                                                     tm [(u, aq)]
                                                     FStar_Pervasives_Native.None
                                                     tm.FStar_Syntax_Syntax.pos
                                                    in
                                                 let typ' =
                                                   let uu____2934 =
                                                     comp_to_typ c  in
                                                   FStar_All.pipe_left
                                                     (FStar_Syntax_Subst.subst
                                                        [FStar_Syntax_Syntax.NT
                                                           (bv, u)])
                                                     uu____2934
                                                    in
                                                 let uu____2935 =
                                                   __apply uopt tm' typ'  in
                                                 bind uu____2935
                                                   (fun uu____2943  ->
                                                      let u1 =
                                                        bnorm
                                                          goal.FStar_Tactics_Types.context
                                                          u
                                                         in
                                                      let uu____2945 =
                                                        let uu____2946 =
                                                          let uu____2949 =
                                                            let uu____2950 =
                                                              FStar_Syntax_Util.head_and_args
                                                                u1
                                                               in
                                                            FStar_Pervasives_Native.fst
                                                              uu____2950
                                                             in
                                                          FStar_Syntax_Subst.compress
                                                            uu____2949
                                                           in
                                                        uu____2946.FStar_Syntax_Syntax.n
                                                         in
                                                      match uu____2945 with
                                                      | FStar_Syntax_Syntax.Tm_uvar
                                                          (uvar,uu____2978)
                                                          ->
                                                          bind get
                                                            (fun ps  ->
                                                               let uu____3006
                                                                 =
                                                                 uopt &&
                                                                   (uvar_free
                                                                    uvar ps)
                                                                  in
                                                               if uu____3006
                                                               then ret ()
                                                               else
                                                                 (let uu____3010
                                                                    =
                                                                    let uu____3013
                                                                    =
                                                                    let uu___85_3014
                                                                    = goal
                                                                     in
                                                                    let uu____3015
                                                                    =
                                                                    bnorm
                                                                    goal.FStar_Tactics_Types.context
                                                                    u1  in
                                                                    let uu____3016
                                                                    =
                                                                    bnorm
                                                                    goal.FStar_Tactics_Types.context
                                                                    bv.FStar_Syntax_Syntax.sort
                                                                     in
                                                                    {
                                                                    FStar_Tactics_Types.context
                                                                    =
                                                                    (uu___85_3014.FStar_Tactics_Types.context);
                                                                    FStar_Tactics_Types.witness
                                                                    =
                                                                    uu____3015;
                                                                    FStar_Tactics_Types.goal_ty
                                                                    =
                                                                    uu____3016;
                                                                    FStar_Tactics_Types.opts
                                                                    =
                                                                    (uu___85_3014.FStar_Tactics_Types.opts);
                                                                    FStar_Tactics_Types.is_guard
                                                                    = false
                                                                    }  in
                                                                    [uu____3013]
                                                                     in
                                                                  add_goals
                                                                    uu____3010))
                                                      | t -> ret ()))))))))
  
let try_unif : 'a . 'a tac -> 'a tac -> 'a tac =
  fun t  ->
    fun t'  -> mk_tac (fun ps  -> try run t ps with | NoUnif  -> run t' ps)
  
let (apply : Prims.bool -> FStar_Syntax_Syntax.term -> Prims.unit tac) =
  fun uopt  ->
    fun tm  ->
      let uu____3062 =
        mlog
          (fun uu____3067  ->
             let uu____3068 = FStar_Syntax_Print.term_to_string tm  in
             FStar_Util.print1 "apply: tm = %s\n" uu____3068)
          (fun uu____3070  ->
             bind cur_goal
               (fun goal  ->
                  let uu____3074 = __tc goal.FStar_Tactics_Types.context tm
                     in
                  bind uu____3074
                    (fun uu____3096  ->
                       match uu____3096 with
                       | (tm1,typ,guard) ->
                           let typ1 =
                             bnorm goal.FStar_Tactics_Types.context typ  in
                           let uu____3109 =
                             let uu____3112 =
                               let uu____3115 = __apply uopt tm1 typ1  in
                               bind uu____3115
                                 (fun uu____3119  ->
                                    proc_guard "apply guard"
                                      goal.FStar_Tactics_Types.context guard
                                      goal.FStar_Tactics_Types.opts)
                                in
                             focus uu____3112  in
                           let uu____3120 =
                             let uu____3123 =
                               tts goal.FStar_Tactics_Types.context tm1  in
                             let uu____3124 =
                               tts goal.FStar_Tactics_Types.context typ1  in
                             let uu____3125 =
                               tts goal.FStar_Tactics_Types.context
                                 goal.FStar_Tactics_Types.goal_ty
                                in
                             fail3
                               "Cannot instantiate %s (of type %s) to match goal (%s)"
                               uu____3123 uu____3124 uu____3125
                              in
                           try_unif uu____3109 uu____3120)))
         in
      FStar_All.pipe_left (wrap_err "apply") uu____3062
  
let (apply_lemma : FStar_Syntax_Syntax.term -> Prims.unit tac) =
  fun tm  ->
    let uu____3137 =
      let uu____3140 =
        mlog
          (fun uu____3145  ->
             let uu____3146 = FStar_Syntax_Print.term_to_string tm  in
             FStar_Util.print1 "apply_lemma: tm = %s\n" uu____3146)
          (fun uu____3149  ->
             let is_unit_t t =
               let uu____3154 =
                 let uu____3155 = FStar_Syntax_Subst.compress t  in
                 uu____3155.FStar_Syntax_Syntax.n  in
               match uu____3154 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.unit_lid
                   -> true
               | uu____3159 -> false  in
             bind cur_goal
               (fun goal  ->
                  let uu____3163 = __tc goal.FStar_Tactics_Types.context tm
                     in
                  bind uu____3163
                    (fun uu____3185  ->
                       match uu____3185 with
                       | (tm1,t,guard) ->
                           let uu____3197 =
                             FStar_Syntax_Util.arrow_formals_comp t  in
                           (match uu____3197 with
                            | (bs,comp) ->
                                if
                                  Prims.op_Negation
                                    (FStar_Syntax_Util.is_lemma_comp comp)
                                then fail "not a lemma"
                                else
                                  (let uu____3227 =
                                     FStar_List.fold_left
                                       (fun uu____3273  ->
                                          fun uu____3274  ->
                                            match (uu____3273, uu____3274)
                                            with
                                            | ((uvs,guard1,subst1),(b,aq)) ->
                                                let b_t =
                                                  FStar_Syntax_Subst.subst
                                                    subst1
                                                    b.FStar_Syntax_Syntax.sort
                                                   in
                                                let uu____3377 =
                                                  is_unit_t b_t  in
                                                if uu____3377
                                                then
                                                  (((FStar_Syntax_Util.exp_unit,
                                                      aq) :: uvs), guard1,
                                                    ((FStar_Syntax_Syntax.NT
                                                        (b,
                                                          FStar_Syntax_Util.exp_unit))
                                                    :: subst1))
                                                else
                                                  (let uu____3415 =
                                                     FStar_TypeChecker_Util.new_implicit_var
                                                       "apply_lemma"
                                                       (goal.FStar_Tactics_Types.goal_ty).FStar_Syntax_Syntax.pos
                                                       goal.FStar_Tactics_Types.context
                                                       b_t
                                                      in
                                                   match uu____3415 with
                                                   | (u,uu____3445,g_u) ->
                                                       let uu____3459 =
                                                         FStar_TypeChecker_Rel.conj_guard
                                                           guard1 g_u
                                                          in
                                                       (((u, aq) :: uvs),
                                                         uu____3459,
                                                         ((FStar_Syntax_Syntax.NT
                                                             (b, u)) ::
                                                         subst1))))
                                       ([], guard, []) bs
                                      in
                                   match uu____3227 with
                                   | (uvs,implicits,subst1) ->
                                       let uvs1 = FStar_List.rev uvs  in
                                       let comp1 =
                                         FStar_Syntax_Subst.subst_comp subst1
                                           comp
                                          in
                                       let uu____3529 =
                                         let uu____3538 =
                                           let uu____3547 =
                                             FStar_Syntax_Util.comp_to_comp_typ
                                               comp1
                                              in
                                           uu____3547.FStar_Syntax_Syntax.effect_args
                                            in
                                         match uu____3538 with
                                         | pre::post::uu____3558 ->
                                             ((FStar_Pervasives_Native.fst
                                                 pre),
                                               (FStar_Pervasives_Native.fst
                                                  post))
                                         | uu____3599 ->
                                             failwith
                                               "apply_lemma: impossible: not a lemma"
                                          in
                                       (match uu____3529 with
                                        | (pre,post) ->
                                            let post1 =
                                              let uu____3631 =
                                                let uu____3640 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    FStar_Syntax_Util.exp_unit
                                                   in
                                                [uu____3640]  in
                                              FStar_Syntax_Util.mk_app post
                                                uu____3631
                                               in
                                            let uu____3641 =
                                              let uu____3644 =
                                                FStar_Syntax_Util.mk_squash
                                                  FStar_Syntax_Syntax.U_zero
                                                  post1
                                                 in
                                              do_unify
                                                goal.FStar_Tactics_Types.context
                                                uu____3644
                                                goal.FStar_Tactics_Types.goal_ty
                                               in
                                            bind uu____3641
                                              (fun b  ->
                                                 if Prims.op_Negation b
                                                 then
                                                   let uu____3652 =
                                                     tts
                                                       goal.FStar_Tactics_Types.context
                                                       tm1
                                                      in
                                                   let uu____3653 =
                                                     let uu____3654 =
                                                       FStar_Syntax_Util.mk_squash
                                                         FStar_Syntax_Syntax.U_zero
                                                         post1
                                                        in
                                                     tts
                                                       goal.FStar_Tactics_Types.context
                                                       uu____3654
                                                      in
                                                   let uu____3655 =
                                                     tts
                                                       goal.FStar_Tactics_Types.context
                                                       goal.FStar_Tactics_Types.goal_ty
                                                      in
                                                   fail3
                                                     "Cannot instantiate lemma %s (with postcondition: %s) to match goal (%s)"
                                                     uu____3652 uu____3653
                                                     uu____3655
                                                 else
                                                   (let uu____3657 =
                                                      add_implicits
                                                        implicits.FStar_TypeChecker_Env.implicits
                                                       in
                                                    bind uu____3657
                                                      (fun uu____3662  ->
                                                         let uu____3663 =
                                                           solve goal
                                                             FStar_Syntax_Util.exp_unit
                                                            in
                                                         bind uu____3663
                                                           (fun uu____3671 
                                                              ->
                                                              let is_free_uvar
                                                                uv t1 =
                                                                let free_uvars
                                                                  =
                                                                  let uu____3682
                                                                    =
                                                                    let uu____3689
                                                                    =
                                                                    FStar_Syntax_Free.uvars
                                                                    t1  in
                                                                    FStar_Util.set_elements
                                                                    uu____3689
                                                                     in
                                                                  FStar_List.map
                                                                    FStar_Pervasives_Native.fst
                                                                    uu____3682
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
                                                                let uu____3730
                                                                  =
                                                                  FStar_Syntax_Util.head_and_args
                                                                    t1
                                                                   in
                                                                match uu____3730
                                                                with
                                                                | (hd1,uu____3746)
                                                                    ->
                                                                    (
                                                                    match 
                                                                    hd1.FStar_Syntax_Syntax.n
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Tm_uvar
                                                                    (uv,uu____3768)
                                                                    ->
                                                                    appears
                                                                    uv goals
                                                                    | 
                                                                    uu____3793
                                                                    -> false)
                                                                 in
                                                              let uu____3794
                                                                =
                                                                FStar_All.pipe_right
                                                                  implicits.FStar_TypeChecker_Env.implicits
                                                                  (mapM
                                                                    (fun
                                                                    uu____3866
                                                                     ->
                                                                    match uu____3866
                                                                    with
                                                                    | 
                                                                    (_msg,env,_uvar,term,typ,uu____3894)
                                                                    ->
                                                                    let uu____3895
                                                                    =
                                                                    FStar_Syntax_Util.head_and_args
                                                                    term  in
                                                                    (match uu____3895
                                                                    with
                                                                    | 
                                                                    (hd1,uu____3921)
                                                                    ->
                                                                    let uu____3942
                                                                    =
                                                                    let uu____3943
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    hd1  in
                                                                    uu____3943.FStar_Syntax_Syntax.n
                                                                     in
                                                                    (match uu____3942
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Tm_uvar
                                                                    uu____3956
                                                                    ->
                                                                    let uu____3973
                                                                    =
                                                                    let uu____3982
                                                                    =
                                                                    let uu____3985
                                                                    =
                                                                    let uu___88_3986
                                                                    = goal
                                                                     in
                                                                    let uu____3987
                                                                    =
                                                                    bnorm
                                                                    goal.FStar_Tactics_Types.context
                                                                    term  in
                                                                    let uu____3988
                                                                    =
                                                                    bnorm
                                                                    goal.FStar_Tactics_Types.context
                                                                    typ  in
                                                                    {
                                                                    FStar_Tactics_Types.context
                                                                    =
                                                                    (uu___88_3986.FStar_Tactics_Types.context);
                                                                    FStar_Tactics_Types.witness
                                                                    =
                                                                    uu____3987;
                                                                    FStar_Tactics_Types.goal_ty
                                                                    =
                                                                    uu____3988;
                                                                    FStar_Tactics_Types.opts
                                                                    =
                                                                    (uu___88_3986.FStar_Tactics_Types.opts);
                                                                    FStar_Tactics_Types.is_guard
                                                                    =
                                                                    (uu___88_3986.FStar_Tactics_Types.is_guard)
                                                                    }  in
                                                                    [uu____3985]
                                                                     in
                                                                    (uu____3982,
                                                                    [])  in
                                                                    ret
                                                                    uu____3973
                                                                    | 
                                                                    uu____4001
                                                                    ->
                                                                    let g_typ
                                                                    =
                                                                    let uu____4003
                                                                    =
                                                                    FStar_Options.__temp_fast_implicits
                                                                    ()  in
                                                                    if
                                                                    uu____4003
                                                                    then
                                                                    FStar_TypeChecker_TcTerm.check_type_of_well_typed_term
                                                                    false env
                                                                    term typ
                                                                    else
                                                                    (let term1
                                                                    =
                                                                    bnorm env
                                                                    term  in
                                                                    let uu____4006
                                                                    =
                                                                    let uu____4013
                                                                    =
                                                                    FStar_TypeChecker_Env.set_expected_typ
                                                                    env typ
                                                                     in
                                                                    env.FStar_TypeChecker_Env.type_of
                                                                    uu____4013
                                                                    term1  in
                                                                    match uu____4006
                                                                    with
                                                                    | 
                                                                    (uu____4014,uu____4015,g_typ)
                                                                    -> g_typ)
                                                                     in
                                                                    let uu____4017
                                                                    =
                                                                    goal_from_guard
                                                                    "apply_lemma solved arg"
                                                                    goal.FStar_Tactics_Types.context
                                                                    g_typ
                                                                    goal.FStar_Tactics_Types.opts
                                                                     in
                                                                    bind
                                                                    uu____4017
                                                                    (fun
                                                                    uu___58_4033
                                                                     ->
                                                                    match uu___58_4033
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
                                                              bind uu____3794
                                                                (fun goals_ 
                                                                   ->
                                                                   let sub_goals
                                                                    =
                                                                    let uu____4101
                                                                    =
                                                                    FStar_List.map
                                                                    FStar_Pervasives_Native.fst
                                                                    goals_
                                                                     in
                                                                    FStar_List.flatten
                                                                    uu____4101
                                                                     in
                                                                   let smt_goals
                                                                    =
                                                                    let uu____4123
                                                                    =
                                                                    FStar_List.map
                                                                    FStar_Pervasives_Native.snd
                                                                    goals_
                                                                     in
                                                                    FStar_List.flatten
                                                                    uu____4123
                                                                     in
                                                                   let rec filter'
                                                                    a f xs =
                                                                    match xs
                                                                    with
                                                                    | 
                                                                    [] -> []
                                                                    | 
                                                                    x::xs1 ->
                                                                    let uu____4178
                                                                    = f x xs1
                                                                     in
                                                                    if
                                                                    uu____4178
                                                                    then
                                                                    let uu____4181
                                                                    =
                                                                    filter'
                                                                    () f xs1
                                                                     in x ::
                                                                    uu____4181
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
                                                                    let uu____4195
                                                                    =
                                                                    checkone
                                                                    g.FStar_Tactics_Types.witness
                                                                    goals  in
                                                                    Prims.op_Negation
                                                                    uu____4195))
                                                                    a438 a439)
                                                                    (Obj.magic
                                                                    sub_goals))
                                                                     in
                                                                   let uu____4196
                                                                    =
                                                                    proc_guard
                                                                    "apply_lemma guard"
                                                                    goal.FStar_Tactics_Types.context
                                                                    guard
                                                                    goal.FStar_Tactics_Types.opts
                                                                     in
                                                                   bind
                                                                    uu____4196
                                                                    (fun
                                                                    uu____4201
                                                                     ->
                                                                    let uu____4202
                                                                    =
                                                                    let uu____4205
                                                                    =
                                                                    let uu____4206
                                                                    =
                                                                    let uu____4207
                                                                    =
                                                                    FStar_Syntax_Util.mk_squash
                                                                    FStar_Syntax_Syntax.U_zero
                                                                    pre  in
                                                                    istrivial
                                                                    goal.FStar_Tactics_Types.context
                                                                    uu____4207
                                                                     in
                                                                    Prims.op_Negation
                                                                    uu____4206
                                                                     in
                                                                    if
                                                                    uu____4205
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
                                                                    uu____4202
                                                                    (fun
                                                                    uu____4213
                                                                     ->
                                                                    let uu____4214
                                                                    =
                                                                    add_smt_goals
                                                                    smt_goals
                                                                     in
                                                                    bind
                                                                    uu____4214
                                                                    (fun
                                                                    uu____4218
                                                                     ->
                                                                    add_goals
                                                                    sub_goals1))))))))))))))
         in
      focus uu____3140  in
    FStar_All.pipe_left (wrap_err "apply_lemma") uu____3137
  
let (destruct_eq' :
  FStar_Syntax_Syntax.typ ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun typ  ->
    let uu____4238 = FStar_Syntax_Util.destruct_typ_as_formula typ  in
    match uu____4238 with
    | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn
        (l,uu____4248::(e1,uu____4250)::(e2,uu____4252)::[])) when
        FStar_Ident.lid_equals l FStar_Parser_Const.eq2_lid ->
        FStar_Pervasives_Native.Some (e1, e2)
    | uu____4311 -> FStar_Pervasives_Native.None
  
let (destruct_eq :
  FStar_Syntax_Syntax.typ ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun typ  ->
    let uu____4333 = destruct_eq' typ  in
    match uu____4333 with
    | FStar_Pervasives_Native.Some t -> FStar_Pervasives_Native.Some t
    | FStar_Pervasives_Native.None  ->
        let uu____4363 = FStar_Syntax_Util.un_squash typ  in
        (match uu____4363 with
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
        let uu____4419 = FStar_TypeChecker_Env.pop_bv e1  in
        match uu____4419 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (bv',e') ->
            if FStar_Syntax_Syntax.bv_eq bvar bv'
            then FStar_Pervasives_Native.Some (e', [])
            else
              (let uu____4467 = aux e'  in
               FStar_Util.map_opt uu____4467
                 (fun uu____4491  ->
                    match uu____4491 with | (e'',bvs) -> (e'', (bv' :: bvs))))
         in
      let uu____4512 = aux e  in
      FStar_Util.map_opt uu____4512
        (fun uu____4536  ->
           match uu____4536 with | (e',bvs) -> (e', (FStar_List.rev bvs)))
  
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
          let uu____4591 = split_env b1 g.FStar_Tactics_Types.context  in
          FStar_Util.map_opt uu____4591
            (fun uu____4615  ->
               match uu____4615 with
               | (e0,bvs) ->
                   let s1 bv =
                     let uu___89_4632 = bv  in
                     let uu____4633 =
                       FStar_Syntax_Subst.subst s bv.FStar_Syntax_Syntax.sort
                        in
                     {
                       FStar_Syntax_Syntax.ppname =
                         (uu___89_4632.FStar_Syntax_Syntax.ppname);
                       FStar_Syntax_Syntax.index =
                         (uu___89_4632.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort = uu____4633
                     }  in
                   let bvs1 = FStar_List.map s1 bvs  in
                   let c = push_bvs e0 (b2 :: bvs1)  in
                   let w =
                     FStar_Syntax_Subst.subst s g.FStar_Tactics_Types.witness
                      in
                   let t =
                     FStar_Syntax_Subst.subst s g.FStar_Tactics_Types.goal_ty
                      in
                   let uu___90_4642 = g  in
                   {
                     FStar_Tactics_Types.context = c;
                     FStar_Tactics_Types.witness = w;
                     FStar_Tactics_Types.goal_ty = t;
                     FStar_Tactics_Types.opts =
                       (uu___90_4642.FStar_Tactics_Types.opts);
                     FStar_Tactics_Types.is_guard =
                       (uu___90_4642.FStar_Tactics_Types.is_guard)
                   })
  
let (rewrite : FStar_Syntax_Syntax.binder -> Prims.unit tac) =
  fun h  ->
    bind cur_goal
      (fun goal  ->
         let uu____4655 = h  in
         match uu____4655 with
         | (bv,uu____4659) ->
             mlog
               (fun uu____4663  ->
                  let uu____4664 = FStar_Syntax_Print.bv_to_string bv  in
                  let uu____4665 =
                    tts goal.FStar_Tactics_Types.context
                      bv.FStar_Syntax_Syntax.sort
                     in
                  FStar_Util.print2 "+++Rewrite %s : %s\n" uu____4664
                    uu____4665)
               (fun uu____4668  ->
                  let uu____4669 =
                    split_env bv goal.FStar_Tactics_Types.context  in
                  match uu____4669 with
                  | FStar_Pervasives_Native.None  ->
                      fail "rewrite: binder not found in environment"
                  | FStar_Pervasives_Native.Some (e0,bvs) ->
                      let uu____4698 =
                        destruct_eq bv.FStar_Syntax_Syntax.sort  in
                      (match uu____4698 with
                       | FStar_Pervasives_Native.Some (x,e) ->
                           let uu____4713 =
                             let uu____4714 = FStar_Syntax_Subst.compress x
                                in
                             uu____4714.FStar_Syntax_Syntax.n  in
                           (match uu____4713 with
                            | FStar_Syntax_Syntax.Tm_name x1 ->
                                let s = [FStar_Syntax_Syntax.NT (x1, e)]  in
                                let s1 bv1 =
                                  let uu___91_4727 = bv1  in
                                  let uu____4728 =
                                    FStar_Syntax_Subst.subst s
                                      bv1.FStar_Syntax_Syntax.sort
                                     in
                                  {
                                    FStar_Syntax_Syntax.ppname =
                                      (uu___91_4727.FStar_Syntax_Syntax.ppname);
                                    FStar_Syntax_Syntax.index =
                                      (uu___91_4727.FStar_Syntax_Syntax.index);
                                    FStar_Syntax_Syntax.sort = uu____4728
                                  }  in
                                let bvs1 = FStar_List.map s1 bvs  in
                                let uu____4734 =
                                  let uu___92_4735 = goal  in
                                  let uu____4736 = push_bvs e0 (bv :: bvs1)
                                     in
                                  let uu____4737 =
                                    FStar_Syntax_Subst.subst s
                                      goal.FStar_Tactics_Types.witness
                                     in
                                  let uu____4738 =
                                    FStar_Syntax_Subst.subst s
                                      goal.FStar_Tactics_Types.goal_ty
                                     in
                                  {
                                    FStar_Tactics_Types.context = uu____4736;
                                    FStar_Tactics_Types.witness = uu____4737;
                                    FStar_Tactics_Types.goal_ty = uu____4738;
                                    FStar_Tactics_Types.opts =
                                      (uu___92_4735.FStar_Tactics_Types.opts);
                                    FStar_Tactics_Types.is_guard =
                                      (uu___92_4735.FStar_Tactics_Types.is_guard)
                                  }  in
                                replace_cur uu____4734
                            | uu____4739 ->
                                fail
                                  "rewrite: Not an equality hypothesis with a variable on the LHS")
                       | uu____4740 ->
                           fail "rewrite: Not an equality hypothesis")))
  
let (rename_to :
  FStar_Syntax_Syntax.binder -> Prims.string -> Prims.unit tac) =
  fun b  ->
    fun s  ->
      bind cur_goal
        (fun goal  ->
           let uu____4765 = b  in
           match uu____4765 with
           | (bv,uu____4769) ->
               let bv' =
                 FStar_Syntax_Syntax.freshen_bv
                   (let uu___93_4773 = bv  in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (FStar_Ident.mk_ident
                           (s,
                             ((bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange)));
                      FStar_Syntax_Syntax.index =
                        (uu___93_4773.FStar_Syntax_Syntax.index);
                      FStar_Syntax_Syntax.sort =
                        (uu___93_4773.FStar_Syntax_Syntax.sort)
                    })
                  in
               let s1 =
                 let uu____4777 =
                   let uu____4778 =
                     let uu____4785 = FStar_Syntax_Syntax.bv_to_name bv'  in
                     (bv, uu____4785)  in
                   FStar_Syntax_Syntax.NT uu____4778  in
                 [uu____4777]  in
               let uu____4786 = subst_goal bv bv' s1 goal  in
               (match uu____4786 with
                | FStar_Pervasives_Native.None  ->
                    fail "rename_to: binder not found in environment"
                | FStar_Pervasives_Native.Some goal1 -> replace_cur goal1))
  
let (binder_retype : FStar_Syntax_Syntax.binder -> Prims.unit tac) =
  fun b  ->
    bind cur_goal
      (fun goal  ->
         let uu____4805 = b  in
         match uu____4805 with
         | (bv,uu____4809) ->
             let uu____4810 = split_env bv goal.FStar_Tactics_Types.context
                in
             (match uu____4810 with
              | FStar_Pervasives_Native.None  ->
                  fail "binder_retype: binder is not present in environment"
              | FStar_Pervasives_Native.Some (e0,bvs) ->
                  let uu____4839 = FStar_Syntax_Util.type_u ()  in
                  (match uu____4839 with
                   | (ty,u) ->
                       let uu____4848 = new_uvar "binder_retype" e0 ty  in
                       bind uu____4848
                         (fun t'  ->
                            let bv'' =
                              let uu___94_4858 = bv  in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___94_4858.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___94_4858.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = t'
                              }  in
                            let s =
                              let uu____4862 =
                                let uu____4863 =
                                  let uu____4870 =
                                    FStar_Syntax_Syntax.bv_to_name bv''  in
                                  (bv, uu____4870)  in
                                FStar_Syntax_Syntax.NT uu____4863  in
                              [uu____4862]  in
                            let bvs1 =
                              FStar_List.map
                                (fun b1  ->
                                   let uu___95_4878 = b1  in
                                   let uu____4879 =
                                     FStar_Syntax_Subst.subst s
                                       b1.FStar_Syntax_Syntax.sort
                                      in
                                   {
                                     FStar_Syntax_Syntax.ppname =
                                       (uu___95_4878.FStar_Syntax_Syntax.ppname);
                                     FStar_Syntax_Syntax.index =
                                       (uu___95_4878.FStar_Syntax_Syntax.index);
                                     FStar_Syntax_Syntax.sort = uu____4879
                                   }) bvs
                               in
                            let env' = push_bvs e0 (bv'' :: bvs1)  in
                            bind dismiss
                              (fun uu____4885  ->
                                 let uu____4886 =
                                   let uu____4889 =
                                     let uu____4892 =
                                       let uu___96_4893 = goal  in
                                       let uu____4894 =
                                         FStar_Syntax_Subst.subst s
                                           goal.FStar_Tactics_Types.witness
                                          in
                                       let uu____4895 =
                                         FStar_Syntax_Subst.subst s
                                           goal.FStar_Tactics_Types.goal_ty
                                          in
                                       {
                                         FStar_Tactics_Types.context = env';
                                         FStar_Tactics_Types.witness =
                                           uu____4894;
                                         FStar_Tactics_Types.goal_ty =
                                           uu____4895;
                                         FStar_Tactics_Types.opts =
                                           (uu___96_4893.FStar_Tactics_Types.opts);
                                         FStar_Tactics_Types.is_guard =
                                           (uu___96_4893.FStar_Tactics_Types.is_guard)
                                       }  in
                                     [uu____4892]  in
                                   add_goals uu____4889  in
                                 bind uu____4886
                                   (fun uu____4898  ->
                                      let uu____4899 =
                                        FStar_Syntax_Util.mk_eq2
                                          (FStar_Syntax_Syntax.U_succ u) ty
                                          bv.FStar_Syntax_Syntax.sort t'
                                         in
                                      add_irrelevant_goal
                                        "binder_retype equation" e0
                                        uu____4899
                                        goal.FStar_Tactics_Types.opts))))))
  
let (norm_binder_type :
  FStar_Syntax_Embeddings.norm_step Prims.list ->
    FStar_Syntax_Syntax.binder -> Prims.unit tac)
  =
  fun s  ->
    fun b  ->
      bind cur_goal
        (fun goal  ->
           let uu____4920 = b  in
           match uu____4920 with
           | (bv,uu____4924) ->
               let uu____4925 = split_env bv goal.FStar_Tactics_Types.context
                  in
               (match uu____4925 with
                | FStar_Pervasives_Native.None  ->
                    fail
                      "binder_retype: binder is not present in environment"
                | FStar_Pervasives_Native.Some (e0,bvs) ->
                    let steps =
                      let uu____4957 =
                        FStar_TypeChecker_Normalize.tr_norm_steps s  in
                      FStar_List.append
                        [FStar_TypeChecker_Normalize.Reify;
                        FStar_TypeChecker_Normalize.UnfoldTac] uu____4957
                       in
                    let sort' =
                      normalize steps e0 bv.FStar_Syntax_Syntax.sort  in
                    let bv' =
                      let uu___97_4962 = bv  in
                      {
                        FStar_Syntax_Syntax.ppname =
                          (uu___97_4962.FStar_Syntax_Syntax.ppname);
                        FStar_Syntax_Syntax.index =
                          (uu___97_4962.FStar_Syntax_Syntax.index);
                        FStar_Syntax_Syntax.sort = sort'
                      }  in
                    let env' = push_bvs e0 (bv' :: bvs)  in
                    replace_cur
                      (let uu___98_4966 = goal  in
                       {
                         FStar_Tactics_Types.context = env';
                         FStar_Tactics_Types.witness =
                           (uu___98_4966.FStar_Tactics_Types.witness);
                         FStar_Tactics_Types.goal_ty =
                           (uu___98_4966.FStar_Tactics_Types.goal_ty);
                         FStar_Tactics_Types.opts =
                           (uu___98_4966.FStar_Tactics_Types.opts);
                         FStar_Tactics_Types.is_guard =
                           (uu___98_4966.FStar_Tactics_Types.is_guard)
                       })))
  
let (revert : Prims.unit tac) =
  bind cur_goal
    (fun goal  ->
       let uu____4974 =
         FStar_TypeChecker_Env.pop_bv goal.FStar_Tactics_Types.context  in
       match uu____4974 with
       | FStar_Pervasives_Native.None  -> fail "Cannot revert; empty context"
       | FStar_Pervasives_Native.Some (x,env') ->
           let typ' =
             let uu____4996 =
               FStar_Syntax_Syntax.mk_Total goal.FStar_Tactics_Types.goal_ty
                in
             FStar_Syntax_Util.arrow [(x, FStar_Pervasives_Native.None)]
               uu____4996
              in
           let w' =
             FStar_Syntax_Util.abs [(x, FStar_Pervasives_Native.None)]
               goal.FStar_Tactics_Types.witness FStar_Pervasives_Native.None
              in
           replace_cur
             (let uu___99_5030 = goal  in
              {
                FStar_Tactics_Types.context = env';
                FStar_Tactics_Types.witness = w';
                FStar_Tactics_Types.goal_ty = typ';
                FStar_Tactics_Types.opts =
                  (uu___99_5030.FStar_Tactics_Types.opts);
                FStar_Tactics_Types.is_guard =
                  (uu___99_5030.FStar_Tactics_Types.is_guard)
              }))
  
let (free_in :
  FStar_Syntax_Syntax.bv -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun bv  ->
    fun t  ->
      let uu____5037 = FStar_Syntax_Free.names t  in
      FStar_Util.set_mem bv uu____5037
  
let rec (clear : FStar_Syntax_Syntax.binder -> Prims.unit tac) =
  fun b  ->
    let bv = FStar_Pervasives_Native.fst b  in
    bind cur_goal
      (fun goal  ->
         mlog
           (fun uu____5053  ->
              let uu____5054 = FStar_Syntax_Print.binder_to_string b  in
              let uu____5055 =
                let uu____5056 =
                  let uu____5057 =
                    FStar_TypeChecker_Env.all_binders
                      goal.FStar_Tactics_Types.context
                     in
                  FStar_All.pipe_right uu____5057 FStar_List.length  in
                FStar_All.pipe_right uu____5056 FStar_Util.string_of_int  in
              FStar_Util.print2 "Clear of (%s), env has %s binders\n"
                uu____5054 uu____5055)
           (fun uu____5068  ->
              let uu____5069 = split_env bv goal.FStar_Tactics_Types.context
                 in
              match uu____5069 with
              | FStar_Pervasives_Native.None  ->
                  fail "Cannot clear; binder not in environment"
              | FStar_Pervasives_Native.Some (e',bvs) ->
                  let rec check bvs1 =
                    match bvs1 with
                    | [] -> ret ()
                    | bv'::bvs2 ->
                        let uu____5114 =
                          free_in bv bv'.FStar_Syntax_Syntax.sort  in
                        if uu____5114
                        then
                          let uu____5117 =
                            let uu____5118 =
                              FStar_Syntax_Print.bv_to_string bv'  in
                            FStar_Util.format1
                              "Cannot clear; binder present in the type of %s"
                              uu____5118
                             in
                          fail uu____5117
                        else check bvs2
                     in
                  let uu____5120 =
                    free_in bv goal.FStar_Tactics_Types.goal_ty  in
                  if uu____5120
                  then fail "Cannot clear; binder present in goal"
                  else
                    (let uu____5124 = check bvs  in
                     bind uu____5124
                       (fun uu____5130  ->
                          let env' = push_bvs e' bvs  in
                          let uu____5132 =
                            new_uvar "clear.witness" env'
                              goal.FStar_Tactics_Types.goal_ty
                             in
                          bind uu____5132
                            (fun ut  ->
                               let uu____5138 =
                                 do_unify goal.FStar_Tactics_Types.context
                                   goal.FStar_Tactics_Types.witness ut
                                  in
                               bind uu____5138
                                 (fun b1  ->
                                    if b1
                                    then
                                      replace_cur
                                        (let uu___100_5147 = goal  in
                                         {
                                           FStar_Tactics_Types.context = env';
                                           FStar_Tactics_Types.witness = ut;
                                           FStar_Tactics_Types.goal_ty =
                                             (uu___100_5147.FStar_Tactics_Types.goal_ty);
                                           FStar_Tactics_Types.opts =
                                             (uu___100_5147.FStar_Tactics_Types.opts);
                                           FStar_Tactics_Types.is_guard =
                                             (uu___100_5147.FStar_Tactics_Types.is_guard)
                                         })
                                    else
                                      fail
                                        "Cannot clear; binder appears in witness"))))))
  
let (clear_top : Prims.unit tac) =
  bind cur_goal
    (fun goal  ->
       let uu____5156 =
         FStar_TypeChecker_Env.pop_bv goal.FStar_Tactics_Types.context  in
       match uu____5156 with
       | FStar_Pervasives_Native.None  -> fail "Cannot clear; empty context"
       | FStar_Pervasives_Native.Some (x,uu____5170) ->
           let uu____5175 = FStar_Syntax_Syntax.mk_binder x  in
           clear uu____5175)
  
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
           let uu___101_5191 = g  in
           {
             FStar_Tactics_Types.context = ctx';
             FStar_Tactics_Types.witness =
               (uu___101_5191.FStar_Tactics_Types.witness);
             FStar_Tactics_Types.goal_ty =
               (uu___101_5191.FStar_Tactics_Types.goal_ty);
             FStar_Tactics_Types.opts =
               (uu___101_5191.FStar_Tactics_Types.opts);
             FStar_Tactics_Types.is_guard =
               (uu___101_5191.FStar_Tactics_Types.is_guard)
           }  in
         bind dismiss (fun uu____5193  -> add_goals [g']))
  
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
           let uu___102_5209 = g  in
           {
             FStar_Tactics_Types.context = ctx';
             FStar_Tactics_Types.witness =
               (uu___102_5209.FStar_Tactics_Types.witness);
             FStar_Tactics_Types.goal_ty =
               (uu___102_5209.FStar_Tactics_Types.goal_ty);
             FStar_Tactics_Types.opts =
               (uu___102_5209.FStar_Tactics_Types.opts);
             FStar_Tactics_Types.is_guard =
               (uu___102_5209.FStar_Tactics_Types.is_guard)
           }  in
         bind dismiss (fun uu____5211  -> add_goals [g']))
  
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
            let uu____5243 = FStar_Syntax_Subst.compress t  in
            uu____5243.FStar_Syntax_Syntax.n  in
          let uu____5246 =
            if d = FStar_Tactics_Types.TopDown
            then
              f env
                (let uu___104_5252 = t  in
                 {
                   FStar_Syntax_Syntax.n = tn;
                   FStar_Syntax_Syntax.pos =
                     (uu___104_5252.FStar_Syntax_Syntax.pos);
                   FStar_Syntax_Syntax.vars =
                     (uu___104_5252.FStar_Syntax_Syntax.vars)
                 })
            else ret t  in
          bind uu____5246
            (fun t1  ->
               let tn1 =
                 let uu____5260 =
                   let uu____5261 = FStar_Syntax_Subst.compress t1  in
                   uu____5261.FStar_Syntax_Syntax.n  in
                 match uu____5260 with
                 | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
                     let ff = tac_fold_env d f env  in
                     let uu____5293 = ff hd1  in
                     bind uu____5293
                       (fun hd2  ->
                          let fa uu____5313 =
                            match uu____5313 with
                            | (a,q) ->
                                let uu____5326 = ff a  in
                                bind uu____5326 (fun a1  -> ret (a1, q))
                             in
                          let uu____5339 = mapM fa args  in
                          bind uu____5339
                            (fun args1  ->
                               ret (FStar_Syntax_Syntax.Tm_app (hd2, args1))))
                 | FStar_Syntax_Syntax.Tm_abs (bs,t2,k) ->
                     let uu____5399 = FStar_Syntax_Subst.open_term bs t2  in
                     (match uu____5399 with
                      | (bs1,t') ->
                          let uu____5408 =
                            let uu____5411 =
                              FStar_TypeChecker_Env.push_binders env bs1  in
                            tac_fold_env d f uu____5411 t'  in
                          bind uu____5408
                            (fun t''  ->
                               let uu____5415 =
                                 let uu____5416 =
                                   let uu____5433 =
                                     FStar_Syntax_Subst.close_binders bs1  in
                                   let uu____5434 =
                                     FStar_Syntax_Subst.close bs1 t''  in
                                   (uu____5433, uu____5434, k)  in
                                 FStar_Syntax_Syntax.Tm_abs uu____5416  in
                               ret uu____5415))
                 | FStar_Syntax_Syntax.Tm_arrow (bs,k) -> ret tn
                 | uu____5455 -> ret tn  in
               bind tn1
                 (fun tn2  ->
                    let t' =
                      let uu___103_5462 = t1  in
                      {
                        FStar_Syntax_Syntax.n = tn2;
                        FStar_Syntax_Syntax.pos =
                          (uu___103_5462.FStar_Syntax_Syntax.pos);
                        FStar_Syntax_Syntax.vars =
                          (uu___103_5462.FStar_Syntax_Syntax.vars)
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
            let uu____5491 = FStar_TypeChecker_TcTerm.tc_term env t  in
            match uu____5491 with
            | (t1,lcomp,g) ->
                let uu____5503 =
                  (let uu____5506 =
                     FStar_Syntax_Util.is_pure_or_ghost_lcomp lcomp  in
                   Prims.op_Negation uu____5506) ||
                    (let uu____5508 = FStar_TypeChecker_Rel.is_trivial g  in
                     Prims.op_Negation uu____5508)
                   in
                if uu____5503
                then ret t1
                else
                  (let rewrite_eq =
                     let typ = lcomp.FStar_Syntax_Syntax.res_typ  in
                     let uu____5518 = new_uvar "pointwise_rec" env typ  in
                     bind uu____5518
                       (fun ut  ->
                          log ps
                            (fun uu____5529  ->
                               let uu____5530 =
                                 FStar_Syntax_Print.term_to_string t1  in
                               let uu____5531 =
                                 FStar_Syntax_Print.term_to_string ut  in
                               FStar_Util.print2
                                 "Pointwise_rec: making equality\n\t%s ==\n\t%s\n"
                                 uu____5530 uu____5531);
                          (let uu____5532 =
                             let uu____5535 =
                               let uu____5536 =
                                 FStar_TypeChecker_TcTerm.universe_of env typ
                                  in
                               FStar_Syntax_Util.mk_eq2 uu____5536 typ t1 ut
                                in
                             add_irrelevant_goal "pointwise_rec equation" env
                               uu____5535 opts
                              in
                           bind uu____5532
                             (fun uu____5539  ->
                                let uu____5540 =
                                  bind tau
                                    (fun uu____5546  ->
                                       let ut1 =
                                         FStar_TypeChecker_Normalize.reduce_uvar_solutions
                                           env ut
                                          in
                                       log ps
                                         (fun uu____5552  ->
                                            let uu____5553 =
                                              FStar_Syntax_Print.term_to_string
                                                t1
                                               in
                                            let uu____5554 =
                                              FStar_Syntax_Print.term_to_string
                                                ut1
                                               in
                                            FStar_Util.print2
                                              "Pointwise_rec: succeeded rewriting\n\t%s to\n\t%s\n"
                                              uu____5553 uu____5554);
                                       ret ut1)
                                   in
                                focus uu____5540)))
                      in
                   let uu____5555 = trytac' rewrite_eq  in
                   bind uu____5555
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
          let uu____5703 = FStar_Syntax_Subst.compress t  in
          maybe_continue ctrl uu____5703
            (fun t1  ->
               let uu____5707 =
                 f env
                   (let uu___107_5716 = t1  in
                    {
                      FStar_Syntax_Syntax.n = (t1.FStar_Syntax_Syntax.n);
                      FStar_Syntax_Syntax.pos =
                        (uu___107_5716.FStar_Syntax_Syntax.pos);
                      FStar_Syntax_Syntax.vars =
                        (uu___107_5716.FStar_Syntax_Syntax.vars)
                    })
                  in
               bind uu____5707
                 (fun uu____5728  ->
                    match uu____5728 with
                    | (t2,ctrl1) ->
                        maybe_continue ctrl1 t2
                          (fun t3  ->
                             let uu____5747 =
                               let uu____5748 =
                                 FStar_Syntax_Subst.compress t3  in
                               uu____5748.FStar_Syntax_Syntax.n  in
                             match uu____5747 with
                             | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
                                 let uu____5781 =
                                   ctrl_tac_fold f env ctrl1 hd1  in
                                 bind uu____5781
                                   (fun uu____5806  ->
                                      match uu____5806 with
                                      | (hd2,ctrl2) ->
                                          let ctrl3 = keep_going ctrl2  in
                                          let uu____5822 =
                                            ctrl_tac_fold_args f env ctrl3
                                              args
                                             in
                                          bind uu____5822
                                            (fun uu____5849  ->
                                               match uu____5849 with
                                               | (args1,ctrl4) ->
                                                   ret
                                                     ((let uu___105_5879 = t3
                                                          in
                                                       {
                                                         FStar_Syntax_Syntax.n
                                                           =
                                                           (FStar_Syntax_Syntax.Tm_app
                                                              (hd2, args1));
                                                         FStar_Syntax_Syntax.pos
                                                           =
                                                           (uu___105_5879.FStar_Syntax_Syntax.pos);
                                                         FStar_Syntax_Syntax.vars
                                                           =
                                                           (uu___105_5879.FStar_Syntax_Syntax.vars)
                                                       }), ctrl4)))
                             | FStar_Syntax_Syntax.Tm_abs (bs,t4,k) ->
                                 let uu____5905 =
                                   FStar_Syntax_Subst.open_term bs t4  in
                                 (match uu____5905 with
                                  | (bs1,t') ->
                                      let uu____5920 =
                                        let uu____5927 =
                                          FStar_TypeChecker_Env.push_binders
                                            env bs1
                                           in
                                        ctrl_tac_fold f uu____5927 ctrl1 t'
                                         in
                                      bind uu____5920
                                        (fun uu____5945  ->
                                           match uu____5945 with
                                           | (t'',ctrl2) ->
                                               let uu____5960 =
                                                 let uu____5967 =
                                                   let uu___106_5970 = t4  in
                                                   let uu____5973 =
                                                     let uu____5974 =
                                                       let uu____5991 =
                                                         FStar_Syntax_Subst.close_binders
                                                           bs1
                                                          in
                                                       let uu____5992 =
                                                         FStar_Syntax_Subst.close
                                                           bs1 t''
                                                          in
                                                       (uu____5991,
                                                         uu____5992, k)
                                                        in
                                                     FStar_Syntax_Syntax.Tm_abs
                                                       uu____5974
                                                      in
                                                   {
                                                     FStar_Syntax_Syntax.n =
                                                       uu____5973;
                                                     FStar_Syntax_Syntax.pos
                                                       =
                                                       (uu___106_5970.FStar_Syntax_Syntax.pos);
                                                     FStar_Syntax_Syntax.vars
                                                       =
                                                       (uu___106_5970.FStar_Syntax_Syntax.vars)
                                                   }  in
                                                 (uu____5967, ctrl2)  in
                                               ret uu____5960))
                             | FStar_Syntax_Syntax.Tm_arrow (bs,k) ->
                                 ret (t3, ctrl1)
                             | uu____6025 -> ret (t3, ctrl1))))

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
              let uu____6076 = ctrl_tac_fold f env ctrl t  in
              bind uu____6076
                (fun uu____6104  ->
                   match uu____6104 with
                   | (t1,ctrl1) ->
                       let uu____6123 = ctrl_tac_fold_args f env ctrl1 ts1
                          in
                       bind uu____6123
                         (fun uu____6154  ->
                            match uu____6154 with
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
              let uu____6238 =
                let uu____6245 =
                  add_irrelevant_goal "dummy" env FStar_Syntax_Util.t_true
                    opts
                   in
                bind uu____6245
                  (fun uu____6254  ->
                     let uu____6255 = ctrl t1  in
                     bind uu____6255
                       (fun res  -> bind trivial (fun uu____6282  -> ret res)))
                 in
              bind uu____6238
                (fun uu____6298  ->
                   match uu____6298 with
                   | (should_rewrite,ctrl1) ->
                       if Prims.op_Negation should_rewrite
                       then ret (t1, ctrl1)
                       else
                         (let uu____6322 =
                            FStar_TypeChecker_TcTerm.tc_term env t1  in
                          match uu____6322 with
                          | (t2,lcomp,g) ->
                              let uu____6338 =
                                (let uu____6341 =
                                   FStar_Syntax_Util.is_pure_or_ghost_lcomp
                                     lcomp
                                    in
                                 Prims.op_Negation uu____6341) ||
                                  (let uu____6343 =
                                     FStar_TypeChecker_Rel.is_trivial g  in
                                   Prims.op_Negation uu____6343)
                                 in
                              if uu____6338
                              then ret (t2, globalStop)
                              else
                                (let typ = lcomp.FStar_Syntax_Syntax.res_typ
                                    in
                                 let uu____6358 =
                                   new_uvar "pointwise_rec" env typ  in
                                 bind uu____6358
                                   (fun ut  ->
                                      log ps
                                        (fun uu____6373  ->
                                           let uu____6374 =
                                             FStar_Syntax_Print.term_to_string
                                               t2
                                              in
                                           let uu____6375 =
                                             FStar_Syntax_Print.term_to_string
                                               ut
                                              in
                                           FStar_Util.print2
                                             "Pointwise_rec: making equality\n\t%s ==\n\t%s\n"
                                             uu____6374 uu____6375);
                                      (let uu____6376 =
                                         let uu____6379 =
                                           let uu____6380 =
                                             FStar_TypeChecker_TcTerm.universe_of
                                               env typ
                                              in
                                           FStar_Syntax_Util.mk_eq2
                                             uu____6380 typ t2 ut
                                            in
                                         add_irrelevant_goal
                                           "rewrite_rec equation" env
                                           uu____6379 opts
                                          in
                                       bind uu____6376
                                         (fun uu____6387  ->
                                            let uu____6388 =
                                              bind rewriter
                                                (fun uu____6402  ->
                                                   let ut1 =
                                                     FStar_TypeChecker_Normalize.reduce_uvar_solutions
                                                       env ut
                                                      in
                                                   log ps
                                                     (fun uu____6408  ->
                                                        let uu____6409 =
                                                          FStar_Syntax_Print.term_to_string
                                                            t2
                                                           in
                                                        let uu____6410 =
                                                          FStar_Syntax_Print.term_to_string
                                                            ut1
                                                           in
                                                        FStar_Util.print2
                                                          "rewrite_rec: succeeded rewriting\n\t%s to\n\t%s\n"
                                                          uu____6409
                                                          uu____6410);
                                                   ret (ut1, ctrl1))
                                               in
                                            focus uu____6388))))))
  
let (topdown_rewrite :
  (FStar_Syntax_Syntax.term ->
     (Prims.bool,FStar_BigInt.t) FStar_Pervasives_Native.tuple2 tac)
    -> Prims.unit tac -> Prims.unit tac)
  =
  fun ctrl  ->
    fun rewriter  ->
      bind get
        (fun ps  ->
           let uu____6454 =
             match ps.FStar_Tactics_Types.goals with
             | g::gs -> (g, gs)
             | [] -> failwith "Pointwise: no goals"  in
           match uu____6454 with
           | (g,gs) ->
               let gt1 = g.FStar_Tactics_Types.goal_ty  in
               (log ps
                  (fun uu____6491  ->
                     let uu____6492 = FStar_Syntax_Print.term_to_string gt1
                        in
                     FStar_Util.print1 "Pointwise starting with %s\n"
                       uu____6492);
                bind dismiss_all
                  (fun uu____6495  ->
                     let uu____6496 =
                       ctrl_tac_fold
                         (rewrite_rec ps ctrl rewriter
                            g.FStar_Tactics_Types.opts)
                         g.FStar_Tactics_Types.context keepGoing gt1
                        in
                     bind uu____6496
                       (fun uu____6514  ->
                          match uu____6514 with
                          | (gt',uu____6522) ->
                              (log ps
                                 (fun uu____6526  ->
                                    let uu____6527 =
                                      FStar_Syntax_Print.term_to_string gt'
                                       in
                                    FStar_Util.print1
                                      "Pointwise seems to have succeded with %s\n"
                                      uu____6527);
                               (let uu____6528 = push_goals gs  in
                                bind uu____6528
                                  (fun uu____6532  ->
                                     add_goals
                                       [(let uu___108_6534 = g  in
                                         {
                                           FStar_Tactics_Types.context =
                                             (uu___108_6534.FStar_Tactics_Types.context);
                                           FStar_Tactics_Types.witness =
                                             (uu___108_6534.FStar_Tactics_Types.witness);
                                           FStar_Tactics_Types.goal_ty = gt';
                                           FStar_Tactics_Types.opts =
                                             (uu___108_6534.FStar_Tactics_Types.opts);
                                           FStar_Tactics_Types.is_guard =
                                             (uu___108_6534.FStar_Tactics_Types.is_guard)
                                         })])))))))
  
let (pointwise :
  FStar_Tactics_Types.direction -> Prims.unit tac -> Prims.unit tac) =
  fun d  ->
    fun tau  ->
      bind get
        (fun ps  ->
           let uu____6556 =
             match ps.FStar_Tactics_Types.goals with
             | g::gs -> (g, gs)
             | [] -> failwith "Pointwise: no goals"  in
           match uu____6556 with
           | (g,gs) ->
               let gt1 = g.FStar_Tactics_Types.goal_ty  in
               (log ps
                  (fun uu____6593  ->
                     let uu____6594 = FStar_Syntax_Print.term_to_string gt1
                        in
                     FStar_Util.print1 "Pointwise starting with %s\n"
                       uu____6594);
                bind dismiss_all
                  (fun uu____6597  ->
                     let uu____6598 =
                       tac_fold_env d
                         (pointwise_rec ps tau g.FStar_Tactics_Types.opts)
                         g.FStar_Tactics_Types.context gt1
                        in
                     bind uu____6598
                       (fun gt'  ->
                          log ps
                            (fun uu____6608  ->
                               let uu____6609 =
                                 FStar_Syntax_Print.term_to_string gt'  in
                               FStar_Util.print1
                                 "Pointwise seems to have succeded with %s\n"
                                 uu____6609);
                          (let uu____6610 = push_goals gs  in
                           bind uu____6610
                             (fun uu____6614  ->
                                add_goals
                                  [(let uu___109_6616 = g  in
                                    {
                                      FStar_Tactics_Types.context =
                                        (uu___109_6616.FStar_Tactics_Types.context);
                                      FStar_Tactics_Types.witness =
                                        (uu___109_6616.FStar_Tactics_Types.witness);
                                      FStar_Tactics_Types.goal_ty = gt';
                                      FStar_Tactics_Types.opts =
                                        (uu___109_6616.FStar_Tactics_Types.opts);
                                      FStar_Tactics_Types.is_guard =
                                        (uu___109_6616.FStar_Tactics_Types.is_guard)
                                    })]))))))
  
let (trefl : Prims.unit tac) =
  bind cur_goal
    (fun g  ->
       let uu____6636 =
         FStar_Syntax_Util.un_squash g.FStar_Tactics_Types.goal_ty  in
       match uu____6636 with
       | FStar_Pervasives_Native.Some t ->
           let uu____6648 = FStar_Syntax_Util.head_and_args' t  in
           (match uu____6648 with
            | (hd1,args) ->
                let uu____6681 =
                  let uu____6694 =
                    let uu____6695 = FStar_Syntax_Util.un_uinst hd1  in
                    uu____6695.FStar_Syntax_Syntax.n  in
                  (uu____6694, args)  in
                (match uu____6681 with
                 | (FStar_Syntax_Syntax.Tm_fvar
                    fv,uu____6709::(l,uu____6711)::(r,uu____6713)::[]) when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.eq2_lid
                     ->
                     let uu____6760 =
                       do_unify g.FStar_Tactics_Types.context l r  in
                     bind uu____6760
                       (fun b  ->
                          if Prims.op_Negation b
                          then
                            let uu____6769 =
                              tts g.FStar_Tactics_Types.context l  in
                            let uu____6770 =
                              tts g.FStar_Tactics_Types.context r  in
                            fail2 "trefl: not a trivial equality (%s vs %s)"
                              uu____6769 uu____6770
                          else solve g FStar_Syntax_Util.exp_unit)
                 | (hd2,uu____6773) ->
                     let uu____6790 = tts g.FStar_Tactics_Types.context t  in
                     fail1 "trefl: not an equality (%s)" uu____6790))
       | FStar_Pervasives_Native.None  -> fail "not an irrelevant goal")
  
let (dup : Prims.unit tac) =
  bind cur_goal
    (fun g  ->
       let uu____6800 =
         new_uvar "dup" g.FStar_Tactics_Types.context
           g.FStar_Tactics_Types.goal_ty
          in
       bind uu____6800
         (fun u  ->
            let g' =
              let uu___110_6807 = g  in
              {
                FStar_Tactics_Types.context =
                  (uu___110_6807.FStar_Tactics_Types.context);
                FStar_Tactics_Types.witness = u;
                FStar_Tactics_Types.goal_ty =
                  (uu___110_6807.FStar_Tactics_Types.goal_ty);
                FStar_Tactics_Types.opts =
                  (uu___110_6807.FStar_Tactics_Types.opts);
                FStar_Tactics_Types.is_guard =
                  (uu___110_6807.FStar_Tactics_Types.is_guard)
              }  in
            bind dismiss
              (fun uu____6810  ->
                 let uu____6811 =
                   let uu____6814 =
                     let uu____6815 =
                       FStar_TypeChecker_TcTerm.universe_of
                         g.FStar_Tactics_Types.context
                         g.FStar_Tactics_Types.goal_ty
                        in
                     FStar_Syntax_Util.mk_eq2 uu____6815
                       g.FStar_Tactics_Types.goal_ty u
                       g.FStar_Tactics_Types.witness
                      in
                   add_irrelevant_goal "dup equation"
                     g.FStar_Tactics_Types.context uu____6814
                     g.FStar_Tactics_Types.opts
                    in
                 bind uu____6811
                   (fun uu____6818  ->
                      let uu____6819 = add_goals [g']  in
                      bind uu____6819 (fun uu____6823  -> ret ())))))
  
let (flip : Prims.unit tac) =
  bind get
    (fun ps  ->
       match ps.FStar_Tactics_Types.goals with
       | g1::g2::gs ->
           set
             (let uu___111_6842 = ps  in
              {
                FStar_Tactics_Types.main_context =
                  (uu___111_6842.FStar_Tactics_Types.main_context);
                FStar_Tactics_Types.main_goal =
                  (uu___111_6842.FStar_Tactics_Types.main_goal);
                FStar_Tactics_Types.all_implicits =
                  (uu___111_6842.FStar_Tactics_Types.all_implicits);
                FStar_Tactics_Types.goals = (g2 :: g1 :: gs);
                FStar_Tactics_Types.smt_goals =
                  (uu___111_6842.FStar_Tactics_Types.smt_goals);
                FStar_Tactics_Types.depth =
                  (uu___111_6842.FStar_Tactics_Types.depth);
                FStar_Tactics_Types.__dump =
                  (uu___111_6842.FStar_Tactics_Types.__dump);
                FStar_Tactics_Types.psc =
                  (uu___111_6842.FStar_Tactics_Types.psc);
                FStar_Tactics_Types.entry_range =
                  (uu___111_6842.FStar_Tactics_Types.entry_range);
                FStar_Tactics_Types.guard_policy =
                  (uu___111_6842.FStar_Tactics_Types.guard_policy)
              })
       | uu____6843 -> fail "flip: less than 2 goals")
  
let (later : Prims.unit tac) =
  bind get
    (fun ps  ->
       match ps.FStar_Tactics_Types.goals with
       | [] -> ret ()
       | g::gs ->
           set
             (let uu___112_6860 = ps  in
              {
                FStar_Tactics_Types.main_context =
                  (uu___112_6860.FStar_Tactics_Types.main_context);
                FStar_Tactics_Types.main_goal =
                  (uu___112_6860.FStar_Tactics_Types.main_goal);
                FStar_Tactics_Types.all_implicits =
                  (uu___112_6860.FStar_Tactics_Types.all_implicits);
                FStar_Tactics_Types.goals = (FStar_List.append gs [g]);
                FStar_Tactics_Types.smt_goals =
                  (uu___112_6860.FStar_Tactics_Types.smt_goals);
                FStar_Tactics_Types.depth =
                  (uu___112_6860.FStar_Tactics_Types.depth);
                FStar_Tactics_Types.__dump =
                  (uu___112_6860.FStar_Tactics_Types.__dump);
                FStar_Tactics_Types.psc =
                  (uu___112_6860.FStar_Tactics_Types.psc);
                FStar_Tactics_Types.entry_range =
                  (uu___112_6860.FStar_Tactics_Types.entry_range);
                FStar_Tactics_Types.guard_policy =
                  (uu___112_6860.FStar_Tactics_Types.guard_policy)
              }))
  
let (qed : Prims.unit tac) =
  bind get
    (fun ps  ->
       match ps.FStar_Tactics_Types.goals with
       | [] -> ret ()
       | uu____6869 -> fail "Not done!")
  
let (cases :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 tac)
  =
  fun t  ->
    let uu____6887 =
      bind cur_goal
        (fun g  ->
           let uu____6901 = __tc g.FStar_Tactics_Types.context t  in
           bind uu____6901
             (fun uu____6937  ->
                match uu____6937 with
                | (t1,typ,guard) ->
                    let uu____6953 = FStar_Syntax_Util.head_and_args typ  in
                    (match uu____6953 with
                     | (hd1,args) ->
                         let uu____6996 =
                           let uu____7009 =
                             let uu____7010 = FStar_Syntax_Util.un_uinst hd1
                                in
                             uu____7010.FStar_Syntax_Syntax.n  in
                           (uu____7009, args)  in
                         (match uu____6996 with
                          | (FStar_Syntax_Syntax.Tm_fvar
                             fv,(p,uu____7029)::(q,uu____7031)::[]) when
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
                                let uu___113_7069 = g  in
                                let uu____7070 =
                                  FStar_TypeChecker_Env.push_bv
                                    g.FStar_Tactics_Types.context v_p
                                   in
                                {
                                  FStar_Tactics_Types.context = uu____7070;
                                  FStar_Tactics_Types.witness =
                                    (uu___113_7069.FStar_Tactics_Types.witness);
                                  FStar_Tactics_Types.goal_ty =
                                    (uu___113_7069.FStar_Tactics_Types.goal_ty);
                                  FStar_Tactics_Types.opts =
                                    (uu___113_7069.FStar_Tactics_Types.opts);
                                  FStar_Tactics_Types.is_guard =
                                    (uu___113_7069.FStar_Tactics_Types.is_guard)
                                }  in
                              let g2 =
                                let uu___114_7072 = g  in
                                let uu____7073 =
                                  FStar_TypeChecker_Env.push_bv
                                    g.FStar_Tactics_Types.context v_q
                                   in
                                {
                                  FStar_Tactics_Types.context = uu____7073;
                                  FStar_Tactics_Types.witness =
                                    (uu___114_7072.FStar_Tactics_Types.witness);
                                  FStar_Tactics_Types.goal_ty =
                                    (uu___114_7072.FStar_Tactics_Types.goal_ty);
                                  FStar_Tactics_Types.opts =
                                    (uu___114_7072.FStar_Tactics_Types.opts);
                                  FStar_Tactics_Types.is_guard =
                                    (uu___114_7072.FStar_Tactics_Types.is_guard)
                                }  in
                              bind dismiss
                                (fun uu____7080  ->
                                   let uu____7081 = add_goals [g1; g2]  in
                                   bind uu____7081
                                     (fun uu____7090  ->
                                        let uu____7091 =
                                          let uu____7096 =
                                            FStar_Syntax_Syntax.bv_to_name
                                              v_p
                                             in
                                          let uu____7097 =
                                            FStar_Syntax_Syntax.bv_to_name
                                              v_q
                                             in
                                          (uu____7096, uu____7097)  in
                                        ret uu____7091))
                          | uu____7102 ->
                              let uu____7115 =
                                tts g.FStar_Tactics_Types.context typ  in
                              fail1 "Not a disjunction: %s" uu____7115))))
       in
    FStar_All.pipe_left (wrap_err "cases") uu____6887
  
let (set_options : Prims.string -> Prims.unit tac) =
  fun s  ->
    bind cur_goal
      (fun g  ->
         FStar_Options.push ();
         (let uu____7153 = FStar_Util.smap_copy g.FStar_Tactics_Types.opts
             in
          FStar_Options.set uu____7153);
         (let res = FStar_Options.set_options FStar_Options.Set s  in
          let opts' = FStar_Options.peek ()  in
          FStar_Options.pop ();
          (match res with
           | FStar_Getopt.Success  ->
               let g' =
                 let uu___115_7160 = g  in
                 {
                   FStar_Tactics_Types.context =
                     (uu___115_7160.FStar_Tactics_Types.context);
                   FStar_Tactics_Types.witness =
                     (uu___115_7160.FStar_Tactics_Types.witness);
                   FStar_Tactics_Types.goal_ty =
                     (uu___115_7160.FStar_Tactics_Types.goal_ty);
                   FStar_Tactics_Types.opts = opts';
                   FStar_Tactics_Types.is_guard =
                     (uu___115_7160.FStar_Tactics_Types.is_guard)
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
      let uu____7204 =
        bind cur_goal
          (fun goal  ->
             let env =
               FStar_TypeChecker_Env.set_expected_typ
                 goal.FStar_Tactics_Types.context ty
                in
             let uu____7212 = __tc env tm  in
             bind uu____7212
               (fun uu____7232  ->
                  match uu____7232 with
                  | (tm1,typ,guard) ->
                      (FStar_TypeChecker_Rel.force_trivial_guard env guard;
                       ret tm1)))
         in
      FStar_All.pipe_left (wrap_err "unquote") uu____7204
  
let (uvar_env :
  env ->
    FStar_Syntax_Syntax.typ FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.term tac)
  =
  fun env  ->
    fun ty  ->
      let uu____7263 =
        match ty with
        | FStar_Pervasives_Native.Some ty1 -> ret ty1
        | FStar_Pervasives_Native.None  ->
            let uu____7269 =
              let uu____7270 = FStar_Syntax_Util.type_u ()  in
              FStar_All.pipe_left FStar_Pervasives_Native.fst uu____7270  in
            new_uvar "uvar_env.2" env uu____7269
         in
      bind uu____7263
        (fun typ  ->
           let uu____7282 = new_uvar "uvar_env" env typ  in
           bind uu____7282 (fun t  -> ret t))
  
let (unshelve : FStar_Syntax_Syntax.term -> Prims.unit tac) =
  fun t  ->
    let uu____7294 =
      bind cur_goal
        (fun goal  ->
           let uu____7300 = __tc goal.FStar_Tactics_Types.context t  in
           bind uu____7300
             (fun uu____7320  ->
                match uu____7320 with
                | (t1,typ,guard) ->
                    let uu____7332 =
                      proc_guard "unshelve" goal.FStar_Tactics_Types.context
                        guard goal.FStar_Tactics_Types.opts
                       in
                    bind uu____7332
                      (fun uu____7337  ->
                         let uu____7338 =
                           let uu____7341 =
                             let uu___116_7342 = goal  in
                             let uu____7343 =
                               bnorm goal.FStar_Tactics_Types.context t1  in
                             let uu____7344 =
                               bnorm goal.FStar_Tactics_Types.context typ  in
                             {
                               FStar_Tactics_Types.context =
                                 (uu___116_7342.FStar_Tactics_Types.context);
                               FStar_Tactics_Types.witness = uu____7343;
                               FStar_Tactics_Types.goal_ty = uu____7344;
                               FStar_Tactics_Types.opts =
                                 (uu___116_7342.FStar_Tactics_Types.opts);
                               FStar_Tactics_Types.is_guard = false
                             }  in
                           [uu____7341]  in
                         add_goals uu____7338)))
       in
    FStar_All.pipe_left (wrap_err "unshelve") uu____7294
  
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
          (fun uu____7377  ->
             let uu____7378 = FStar_Options.unsafe_tactic_exec ()  in
             if uu____7378
             then
               let s =
                 FStar_Util.launch_process true "tactic_launch" prog args
                   input (fun uu____7384  -> fun uu____7385  -> false)
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
        (fun uu____7399  ->
           let uu____7400 =
             FStar_Syntax_Syntax.gen_bv nm FStar_Pervasives_Native.None t  in
           ret uu____7400)
  
let (change : FStar_Syntax_Syntax.typ -> Prims.unit tac) =
  fun ty  ->
    let uu____7408 =
      mlog
        (fun uu____7413  ->
           let uu____7414 = FStar_Syntax_Print.term_to_string ty  in
           FStar_Util.print1 "change: ty = %s\n" uu____7414)
        (fun uu____7416  ->
           bind cur_goal
             (fun g  ->
                let uu____7420 = __tc g.FStar_Tactics_Types.context ty  in
                bind uu____7420
                  (fun uu____7440  ->
                     match uu____7440 with
                     | (ty1,uu____7450,guard) ->
                         let uu____7452 =
                           proc_guard "change" g.FStar_Tactics_Types.context
                             guard g.FStar_Tactics_Types.opts
                            in
                         bind uu____7452
                           (fun uu____7457  ->
                              let uu____7458 =
                                do_unify g.FStar_Tactics_Types.context
                                  g.FStar_Tactics_Types.goal_ty ty1
                                 in
                              bind uu____7458
                                (fun bb  ->
                                   if bb
                                   then
                                     replace_cur
                                       (let uu___117_7467 = g  in
                                        {
                                          FStar_Tactics_Types.context =
                                            (uu___117_7467.FStar_Tactics_Types.context);
                                          FStar_Tactics_Types.witness =
                                            (uu___117_7467.FStar_Tactics_Types.witness);
                                          FStar_Tactics_Types.goal_ty = ty1;
                                          FStar_Tactics_Types.opts =
                                            (uu___117_7467.FStar_Tactics_Types.opts);
                                          FStar_Tactics_Types.is_guard =
                                            (uu___117_7467.FStar_Tactics_Types.is_guard)
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
                                      let uu____7474 =
                                        do_unify
                                          g.FStar_Tactics_Types.context ng
                                          nty
                                         in
                                      bind uu____7474
                                        (fun b  ->
                                           if b
                                           then
                                             replace_cur
                                               (let uu___118_7483 = g  in
                                                {
                                                  FStar_Tactics_Types.context
                                                    =
                                                    (uu___118_7483.FStar_Tactics_Types.context);
                                                  FStar_Tactics_Types.witness
                                                    =
                                                    (uu___118_7483.FStar_Tactics_Types.witness);
                                                  FStar_Tactics_Types.goal_ty
                                                    = ty1;
                                                  FStar_Tactics_Types.opts =
                                                    (uu___118_7483.FStar_Tactics_Types.opts);
                                                  FStar_Tactics_Types.is_guard
                                                    =
                                                    (uu___118_7483.FStar_Tactics_Types.is_guard)
                                                })
                                           else fail "not convertible")))))))
       in
    FStar_All.pipe_left (wrap_err "change") uu____7408
  
let (goal_of_goal_ty :
  env ->
    FStar_Syntax_Syntax.typ ->
      (FStar_Tactics_Types.goal,FStar_TypeChecker_Env.guard_t)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun typ  ->
      let uu____7503 =
        FStar_TypeChecker_Util.new_implicit_var "proofstate_of_goal_ty"
          typ.FStar_Syntax_Syntax.pos env typ
         in
      match uu____7503 with
      | (u,uu____7521,g_u) ->
          let g =
            let uu____7536 = FStar_Options.peek ()  in
            {
              FStar_Tactics_Types.context = env;
              FStar_Tactics_Types.witness = u;
              FStar_Tactics_Types.goal_ty = typ;
              FStar_Tactics_Types.opts = uu____7536;
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
      let uu____7547 = goal_of_goal_ty env typ  in
      match uu____7547 with
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
  