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
  
let with_policy : 'a . FStar_Tactics_Types.guard_policy -> 'a tac -> 'a tac =
  fun pol  ->
    fun t  ->
      bind get_guard_policy
        (fun old_pol  ->
           let uu____1537 = set_guard_policy pol  in
           bind uu____1537
             (fun uu____1541  ->
                bind t
                  (fun r  ->
                     let uu____1545 = set_guard_policy old_pol  in
                     bind uu____1545 (fun uu____1549  -> ret r))))
  
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
          let uu____1566 =
            let uu____1567 = FStar_TypeChecker_Rel.simplify_guard e g  in
            uu____1567.FStar_TypeChecker_Env.guard_f  in
          match uu____1566 with
          | FStar_TypeChecker_Common.Trivial  -> ret ()
          | FStar_TypeChecker_Common.NonTrivial f ->
              let uu____1571 = istrivial e f  in
              if uu____1571
              then ret ()
              else
                bind get
                  (fun ps  ->
                     match ps.FStar_Tactics_Types.guard_policy with
                     | FStar_Tactics_Types.Drop  -> ret ()
                     | FStar_Tactics_Types.Goal  ->
                         let uu____1579 = mk_irrelevant_goal reason e f opts
                            in
                         bind uu____1579
                           (fun goal  ->
                              let goal1 =
                                let uu___71_1586 = goal  in
                                {
                                  FStar_Tactics_Types.context =
                                    (uu___71_1586.FStar_Tactics_Types.context);
                                  FStar_Tactics_Types.witness =
                                    (uu___71_1586.FStar_Tactics_Types.witness);
                                  FStar_Tactics_Types.goal_ty =
                                    (uu___71_1586.FStar_Tactics_Types.goal_ty);
                                  FStar_Tactics_Types.opts =
                                    (uu___71_1586.FStar_Tactics_Types.opts);
                                  FStar_Tactics_Types.is_guard = true
                                }  in
                              push_goals [goal1])
                     | FStar_Tactics_Types.SMT  ->
                         let uu____1587 = mk_irrelevant_goal reason e f opts
                            in
                         bind uu____1587
                           (fun goal  ->
                              let goal1 =
                                let uu___72_1594 = goal  in
                                {
                                  FStar_Tactics_Types.context =
                                    (uu___72_1594.FStar_Tactics_Types.context);
                                  FStar_Tactics_Types.witness =
                                    (uu___72_1594.FStar_Tactics_Types.witness);
                                  FStar_Tactics_Types.goal_ty =
                                    (uu___72_1594.FStar_Tactics_Types.goal_ty);
                                  FStar_Tactics_Types.opts =
                                    (uu___72_1594.FStar_Tactics_Types.opts);
                                  FStar_Tactics_Types.is_guard = true
                                }  in
                              push_smt_goals [goal1])
                     | FStar_Tactics_Types.Force  ->
                         (try
                            let uu____1602 =
                              let uu____1603 =
                                let uu____1604 =
                                  FStar_TypeChecker_Rel.discharge_guard_no_smt
                                    e g
                                   in
                                FStar_All.pipe_left
                                  FStar_TypeChecker_Rel.is_trivial uu____1604
                                 in
                              Prims.op_Negation uu____1603  in
                            if uu____1602
                            then
                              mlog
                                (fun uu____1609  ->
                                   let uu____1610 =
                                     FStar_TypeChecker_Rel.guard_to_string e
                                       g
                                      in
                                   FStar_Util.print1 "guard = %s\n"
                                     uu____1610)
                                (fun uu____1612  ->
                                   fail1 "Forcing the guard failed %s)"
                                     reason)
                            else ret ()
                          with
                          | uu____1619 ->
                              mlog
                                (fun uu____1622  ->
                                   let uu____1623 =
                                     FStar_TypeChecker_Rel.guard_to_string e
                                       g
                                      in
                                   FStar_Util.print1 "guard = %s\n"
                                     uu____1623)
                                (fun uu____1625  ->
                                   fail1 "Forcing the guard failed (%s)"
                                     reason)))
  
let (tc : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.typ tac) =
  fun t  ->
    let uu____1633 =
      bind cur_goal
        (fun goal  ->
           let uu____1639 = __tc goal.FStar_Tactics_Types.context t  in
           bind uu____1639
             (fun uu____1659  ->
                match uu____1659 with
                | (t1,typ,guard) ->
                    let uu____1671 =
                      proc_guard "tc" goal.FStar_Tactics_Types.context guard
                        goal.FStar_Tactics_Types.opts
                       in
                    bind uu____1671 (fun uu____1675  -> ret typ)))
       in
    FStar_All.pipe_left (wrap_err "tc") uu____1633
  
let (add_irrelevant_goal :
  Prims.string ->
    env ->
      FStar_Syntax_Syntax.typ -> FStar_Options.optionstate -> Prims.unit tac)
  =
  fun reason  ->
    fun env  ->
      fun phi  ->
        fun opts  ->
          let uu____1696 = mk_irrelevant_goal reason env phi opts  in
          bind uu____1696 (fun goal  -> add_goals [goal])
  
let (trivial : Prims.unit tac) =
  bind cur_goal
    (fun goal  ->
       let uu____1708 =
         istrivial goal.FStar_Tactics_Types.context
           goal.FStar_Tactics_Types.goal_ty
          in
       if uu____1708
       then solve goal FStar_Syntax_Util.exp_unit
       else
         (let uu____1712 =
            tts goal.FStar_Tactics_Types.context
              goal.FStar_Tactics_Types.goal_ty
             in
          fail1 "Not a trivial goal: %s" uu____1712))
  
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
          let uu____1733 =
            let uu____1734 = FStar_TypeChecker_Rel.simplify_guard e g  in
            uu____1734.FStar_TypeChecker_Env.guard_f  in
          match uu____1733 with
          | FStar_TypeChecker_Common.Trivial  ->
              ret FStar_Pervasives_Native.None
          | FStar_TypeChecker_Common.NonTrivial f ->
              let uu____1742 = istrivial e f  in
              if uu____1742
              then ret FStar_Pervasives_Native.None
              else
                (let uu____1750 = mk_irrelevant_goal reason e f opts  in
                 bind uu____1750
                   (fun goal  ->
                      ret
                        (FStar_Pervasives_Native.Some
                           (let uu___75_1760 = goal  in
                            {
                              FStar_Tactics_Types.context =
                                (uu___75_1760.FStar_Tactics_Types.context);
                              FStar_Tactics_Types.witness =
                                (uu___75_1760.FStar_Tactics_Types.witness);
                              FStar_Tactics_Types.goal_ty =
                                (uu___75_1760.FStar_Tactics_Types.goal_ty);
                              FStar_Tactics_Types.opts =
                                (uu___75_1760.FStar_Tactics_Types.opts);
                              FStar_Tactics_Types.is_guard = true
                            }))))
  
let (smt : Prims.unit tac) =
  bind cur_goal
    (fun g  ->
       let uu____1768 = is_irrelevant g  in
       if uu____1768
       then bind dismiss (fun uu____1772  -> add_smt_goals [g])
       else
         (let uu____1774 =
            tts g.FStar_Tactics_Types.context g.FStar_Tactics_Types.goal_ty
             in
          fail1 "goal is not irrelevant: cannot dispatch to smt (%s)"
            uu____1774))
  
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
             let uu____1815 =
               try
                 let uu____1849 =
                   let uu____1858 = FStar_BigInt.to_int_fs n1  in
                   FStar_List.splitAt uu____1858 p.FStar_Tactics_Types.goals
                    in
                 ret uu____1849
               with | uu____1880 -> fail "divide: not enough goals"  in
             bind uu____1815
               (fun uu____1907  ->
                  match uu____1907 with
                  | (lgs,rgs) ->
                      let lp =
                        let uu___76_1933 = p  in
                        {
                          FStar_Tactics_Types.main_context =
                            (uu___76_1933.FStar_Tactics_Types.main_context);
                          FStar_Tactics_Types.main_goal =
                            (uu___76_1933.FStar_Tactics_Types.main_goal);
                          FStar_Tactics_Types.all_implicits =
                            (uu___76_1933.FStar_Tactics_Types.all_implicits);
                          FStar_Tactics_Types.goals = lgs;
                          FStar_Tactics_Types.smt_goals = [];
                          FStar_Tactics_Types.depth =
                            (uu___76_1933.FStar_Tactics_Types.depth);
                          FStar_Tactics_Types.__dump =
                            (uu___76_1933.FStar_Tactics_Types.__dump);
                          FStar_Tactics_Types.psc =
                            (uu___76_1933.FStar_Tactics_Types.psc);
                          FStar_Tactics_Types.entry_range =
                            (uu___76_1933.FStar_Tactics_Types.entry_range);
                          FStar_Tactics_Types.guard_policy =
                            (uu___76_1933.FStar_Tactics_Types.guard_policy)
                        }  in
                      let rp =
                        let uu___77_1935 = p  in
                        {
                          FStar_Tactics_Types.main_context =
                            (uu___77_1935.FStar_Tactics_Types.main_context);
                          FStar_Tactics_Types.main_goal =
                            (uu___77_1935.FStar_Tactics_Types.main_goal);
                          FStar_Tactics_Types.all_implicits =
                            (uu___77_1935.FStar_Tactics_Types.all_implicits);
                          FStar_Tactics_Types.goals = rgs;
                          FStar_Tactics_Types.smt_goals = [];
                          FStar_Tactics_Types.depth =
                            (uu___77_1935.FStar_Tactics_Types.depth);
                          FStar_Tactics_Types.__dump =
                            (uu___77_1935.FStar_Tactics_Types.__dump);
                          FStar_Tactics_Types.psc =
                            (uu___77_1935.FStar_Tactics_Types.psc);
                          FStar_Tactics_Types.entry_range =
                            (uu___77_1935.FStar_Tactics_Types.entry_range);
                          FStar_Tactics_Types.guard_policy =
                            (uu___77_1935.FStar_Tactics_Types.guard_policy)
                        }  in
                      let uu____1936 = set lp  in
                      bind uu____1936
                        (fun uu____1944  ->
                           bind l
                             (fun a  ->
                                bind get
                                  (fun lp'  ->
                                     let uu____1958 = set rp  in
                                     bind uu____1958
                                       (fun uu____1966  ->
                                          bind r
                                            (fun b  ->
                                               bind get
                                                 (fun rp'  ->
                                                    let p' =
                                                      let uu___78_1982 = p
                                                         in
                                                      {
                                                        FStar_Tactics_Types.main_context
                                                          =
                                                          (uu___78_1982.FStar_Tactics_Types.main_context);
                                                        FStar_Tactics_Types.main_goal
                                                          =
                                                          (uu___78_1982.FStar_Tactics_Types.main_goal);
                                                        FStar_Tactics_Types.all_implicits
                                                          =
                                                          (uu___78_1982.FStar_Tactics_Types.all_implicits);
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
                                                          (uu___78_1982.FStar_Tactics_Types.depth);
                                                        FStar_Tactics_Types.__dump
                                                          =
                                                          (uu___78_1982.FStar_Tactics_Types.__dump);
                                                        FStar_Tactics_Types.psc
                                                          =
                                                          (uu___78_1982.FStar_Tactics_Types.psc);
                                                        FStar_Tactics_Types.entry_range
                                                          =
                                                          (uu___78_1982.FStar_Tactics_Types.entry_range);
                                                        FStar_Tactics_Types.guard_policy
                                                          =
                                                          (uu___78_1982.FStar_Tactics_Types.guard_policy)
                                                      }  in
                                                    let uu____1983 = set p'
                                                       in
                                                    bind uu____1983
                                                      (fun uu____1991  ->
                                                         ret (a, b))))))))))
  
let focus : 'a . 'a tac -> 'a tac =
  fun f  ->
    let uu____2009 = divide FStar_BigInt.one f idtac  in
    bind uu____2009
      (fun uu____2022  -> match uu____2022 with | (a,()) -> ret a)
  
let rec map : 'a . 'a tac -> 'a Prims.list tac =
  fun tau  ->
    bind get
      (fun p  ->
         match p.FStar_Tactics_Types.goals with
         | [] -> ret []
         | uu____2056::uu____2057 ->
             let uu____2060 =
               let uu____2069 = map tau  in
               divide FStar_BigInt.one tau uu____2069  in
             bind uu____2060
               (fun uu____2087  ->
                  match uu____2087 with | (h,t) -> ret (h :: t)))
  
let (seq : Prims.unit tac -> Prims.unit tac -> Prims.unit tac) =
  fun t1  ->
    fun t2  ->
      let uu____2124 =
        bind t1
          (fun uu____2129  ->
             let uu____2130 = map t2  in
             bind uu____2130 (fun uu____2138  -> ret ()))
         in
      focus uu____2124
  
let (intro : FStar_Syntax_Syntax.binder tac) =
  let uu____2145 =
    bind cur_goal
      (fun goal  ->
         let uu____2154 =
           FStar_Syntax_Util.arrow_one goal.FStar_Tactics_Types.goal_ty  in
         match uu____2154 with
         | FStar_Pervasives_Native.Some (b,c) ->
             let uu____2169 =
               let uu____2170 = FStar_Syntax_Util.is_total_comp c  in
               Prims.op_Negation uu____2170  in
             if uu____2169
             then fail "Codomain is effectful"
             else
               (let env' =
                  FStar_TypeChecker_Env.push_binders
                    goal.FStar_Tactics_Types.context [b]
                   in
                let typ' = comp_to_typ c  in
                let uu____2176 = new_uvar "intro" env' typ'  in
                bind uu____2176
                  (fun u  ->
                     let uu____2182 =
                       let uu____2185 =
                         FStar_Syntax_Util.abs [b] u
                           FStar_Pervasives_Native.None
                          in
                       trysolve goal uu____2185  in
                     bind uu____2182
                       (fun bb  ->
                          if bb
                          then
                            let uu____2191 =
                              let uu____2194 =
                                let uu___81_2195 = goal  in
                                let uu____2196 = bnorm env' u  in
                                let uu____2197 = bnorm env' typ'  in
                                {
                                  FStar_Tactics_Types.context = env';
                                  FStar_Tactics_Types.witness = uu____2196;
                                  FStar_Tactics_Types.goal_ty = uu____2197;
                                  FStar_Tactics_Types.opts =
                                    (uu___81_2195.FStar_Tactics_Types.opts);
                                  FStar_Tactics_Types.is_guard =
                                    (uu___81_2195.FStar_Tactics_Types.is_guard)
                                }  in
                              replace_cur uu____2194  in
                            bind uu____2191 (fun uu____2199  -> ret b)
                          else fail "unification failed")))
         | FStar_Pervasives_Native.None  ->
             let uu____2205 =
               tts goal.FStar_Tactics_Types.context
                 goal.FStar_Tactics_Types.goal_ty
                in
             fail1 "goal is not an arrow (%s)" uu____2205)
     in
  FStar_All.pipe_left (wrap_err "intro") uu____2145 
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
       (let uu____2236 =
          FStar_Syntax_Util.arrow_one goal.FStar_Tactics_Types.goal_ty  in
        match uu____2236 with
        | FStar_Pervasives_Native.Some (b,c) ->
            let uu____2255 =
              let uu____2256 = FStar_Syntax_Util.is_total_comp c  in
              Prims.op_Negation uu____2256  in
            if uu____2255
            then fail "Codomain is effectful"
            else
              (let bv =
                 FStar_Syntax_Syntax.gen_bv "__recf"
                   FStar_Pervasives_Native.None
                   goal.FStar_Tactics_Types.goal_ty
                  in
               let bs =
                 let uu____2272 = FStar_Syntax_Syntax.mk_binder bv  in
                 [uu____2272; b]  in
               let env' =
                 FStar_TypeChecker_Env.push_binders
                   goal.FStar_Tactics_Types.context bs
                  in
               let uu____2274 =
                 let uu____2277 = comp_to_typ c  in
                 new_uvar "intro_rec" env' uu____2277  in
               bind uu____2274
                 (fun u  ->
                    let lb =
                      let uu____2292 =
                        FStar_Syntax_Util.abs [b] u
                          FStar_Pervasives_Native.None
                         in
                      FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl bv) []
                        goal.FStar_Tactics_Types.goal_ty
                        FStar_Parser_Const.effect_Tot_lid uu____2292 []
                        FStar_Range.dummyRange
                       in
                    let body = FStar_Syntax_Syntax.bv_to_name bv  in
                    let uu____2298 =
                      FStar_Syntax_Subst.close_let_rec [lb] body  in
                    match uu____2298 with
                    | (lbs,body1) ->
                        let tm =
                          FStar_Syntax_Syntax.mk
                            (FStar_Syntax_Syntax.Tm_let ((true, lbs), body1))
                            FStar_Pervasives_Native.None
                            (goal.FStar_Tactics_Types.witness).FStar_Syntax_Syntax.pos
                           in
                        let uu____2328 = trysolve goal tm  in
                        bind uu____2328
                          (fun bb  ->
                             if bb
                             then
                               let uu____2344 =
                                 let uu____2347 =
                                   let uu___82_2348 = goal  in
                                   let uu____2349 = bnorm env' u  in
                                   let uu____2350 =
                                     let uu____2351 = comp_to_typ c  in
                                     bnorm env' uu____2351  in
                                   {
                                     FStar_Tactics_Types.context = env';
                                     FStar_Tactics_Types.witness = uu____2349;
                                     FStar_Tactics_Types.goal_ty = uu____2350;
                                     FStar_Tactics_Types.opts =
                                       (uu___82_2348.FStar_Tactics_Types.opts);
                                     FStar_Tactics_Types.is_guard =
                                       (uu___82_2348.FStar_Tactics_Types.is_guard)
                                   }  in
                                 replace_cur uu____2347  in
                               bind uu____2344
                                 (fun uu____2358  ->
                                    let uu____2359 =
                                      let uu____2364 =
                                        FStar_Syntax_Syntax.mk_binder bv  in
                                      (uu____2364, b)  in
                                    ret uu____2359)
                             else fail "intro_rec: unification failed")))
        | FStar_Pervasives_Native.None  ->
            let uu____2378 =
              tts goal.FStar_Tactics_Types.context
                goal.FStar_Tactics_Types.goal_ty
               in
            fail1 "intro_rec: goal is not an arrow (%s)" uu____2378))
  
let (norm : FStar_Syntax_Embeddings.norm_step Prims.list -> Prims.unit tac) =
  fun s  ->
    bind cur_goal
      (fun goal  ->
         mlog
           (fun uu____2398  ->
              let uu____2399 =
                FStar_Syntax_Print.term_to_string
                  goal.FStar_Tactics_Types.witness
                 in
              FStar_Util.print1 "norm: witness = %s\n" uu____2399)
           (fun uu____2404  ->
              let steps =
                let uu____2408 = FStar_TypeChecker_Normalize.tr_norm_steps s
                   in
                FStar_List.append
                  [FStar_TypeChecker_Normalize.Reify;
                  FStar_TypeChecker_Normalize.UnfoldTac] uu____2408
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
                (let uu___83_2415 = goal  in
                 {
                   FStar_Tactics_Types.context =
                     (uu___83_2415.FStar_Tactics_Types.context);
                   FStar_Tactics_Types.witness = w;
                   FStar_Tactics_Types.goal_ty = t;
                   FStar_Tactics_Types.opts =
                     (uu___83_2415.FStar_Tactics_Types.opts);
                   FStar_Tactics_Types.is_guard =
                     (uu___83_2415.FStar_Tactics_Types.is_guard)
                 })))
  
let (norm_term_env :
  env ->
    FStar_Syntax_Embeddings.norm_step Prims.list ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac)
  =
  fun e  ->
    fun s  ->
      fun t  ->
        let uu____2433 =
          mlog
            (fun uu____2438  ->
               let uu____2439 = FStar_Syntax_Print.term_to_string t  in
               FStar_Util.print1 "norm_term: tm = %s\n" uu____2439)
            (fun uu____2441  ->
               bind get
                 (fun ps  ->
                    let opts =
                      match ps.FStar_Tactics_Types.goals with
                      | g::uu____2447 -> g.FStar_Tactics_Types.opts
                      | uu____2450 -> FStar_Options.peek ()  in
                    mlog
                      (fun uu____2455  ->
                         let uu____2456 =
                           tts ps.FStar_Tactics_Types.main_context t  in
                         FStar_Util.print1 "norm_term_env: t = %s\n"
                           uu____2456)
                      (fun uu____2459  ->
                         let uu____2460 = __tc e t  in
                         bind uu____2460
                           (fun uu____2480  ->
                              match uu____2480 with
                              | (t1,uu____2490,guard) ->
                                  let uu____2492 =
                                    proc_guard "norm_term_env" e guard opts
                                     in
                                  bind uu____2492
                                    (fun uu____2498  ->
                                       let steps =
                                         let uu____2502 =
                                           FStar_TypeChecker_Normalize.tr_norm_steps
                                             s
                                            in
                                         FStar_List.append
                                           [FStar_TypeChecker_Normalize.Reify;
                                           FStar_TypeChecker_Normalize.UnfoldTac]
                                           uu____2502
                                          in
                                       let t2 =
                                         normalize steps
                                           ps.FStar_Tactics_Types.main_context
                                           t1
                                          in
                                       ret t2)))))
           in
        FStar_All.pipe_left (wrap_err "norm_term") uu____2433
  
let (refine_intro : Prims.unit tac) =
  let uu____2514 =
    bind cur_goal
      (fun g  ->
         let uu____2521 =
           FStar_TypeChecker_Rel.base_and_refinement
             g.FStar_Tactics_Types.context g.FStar_Tactics_Types.goal_ty
            in
         match uu____2521 with
         | (uu____2534,FStar_Pervasives_Native.None ) ->
             fail "not a refinement"
         | (t,FStar_Pervasives_Native.Some (bv,phi)) ->
             let g1 =
               let uu___84_2559 = g  in
               {
                 FStar_Tactics_Types.context =
                   (uu___84_2559.FStar_Tactics_Types.context);
                 FStar_Tactics_Types.witness =
                   (uu___84_2559.FStar_Tactics_Types.witness);
                 FStar_Tactics_Types.goal_ty = t;
                 FStar_Tactics_Types.opts =
                   (uu___84_2559.FStar_Tactics_Types.opts);
                 FStar_Tactics_Types.is_guard =
                   (uu___84_2559.FStar_Tactics_Types.is_guard)
               }  in
             let uu____2560 =
               let uu____2565 =
                 let uu____2570 =
                   let uu____2571 = FStar_Syntax_Syntax.mk_binder bv  in
                   [uu____2571]  in
                 FStar_Syntax_Subst.open_term uu____2570 phi  in
               match uu____2565 with
               | (bvs,phi1) ->
                   let uu____2578 =
                     let uu____2579 = FStar_List.hd bvs  in
                     FStar_Pervasives_Native.fst uu____2579  in
                   (uu____2578, phi1)
                in
             (match uu____2560 with
              | (bv1,phi1) ->
                  let uu____2592 =
                    let uu____2595 =
                      FStar_Syntax_Subst.subst
                        [FStar_Syntax_Syntax.NT
                           (bv1, (g.FStar_Tactics_Types.witness))] phi1
                       in
                    mk_irrelevant_goal "refine_intro refinement"
                      g.FStar_Tactics_Types.context uu____2595
                      g.FStar_Tactics_Types.opts
                     in
                  bind uu____2592
                    (fun g2  ->
                       bind dismiss (fun uu____2599  -> add_goals [g1; g2]))))
     in
  FStar_All.pipe_left (wrap_err "refine_intro") uu____2514 
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
           let uu____2620 = __tc env t  in
           bind uu____2620
             (fun uu____2640  ->
                match uu____2640 with
                | (t1,typ,guard) ->
                    let uu____2652 =
                      proc_guard "__exact typing"
                        goal.FStar_Tactics_Types.context guard
                        goal.FStar_Tactics_Types.opts
                       in
                    bind uu____2652
                      (fun uu____2656  ->
                         mlog
                           (fun uu____2660  ->
                              let uu____2661 =
                                tts goal.FStar_Tactics_Types.context typ  in
                              let uu____2662 =
                                tts goal.FStar_Tactics_Types.context
                                  goal.FStar_Tactics_Types.goal_ty
                                 in
                              FStar_Util.print2 "exact: unifying %s and %s\n"
                                uu____2661 uu____2662)
                           (fun uu____2665  ->
                              let uu____2666 =
                                do_unify goal.FStar_Tactics_Types.context typ
                                  goal.FStar_Tactics_Types.goal_ty
                                 in
                              bind uu____2666
                                (fun b  ->
                                   if b
                                   then solve goal t1
                                   else
                                     (let uu____2674 =
                                        tts goal.FStar_Tactics_Types.context
                                          t1
                                         in
                                      let uu____2675 =
                                        tts goal.FStar_Tactics_Types.context
                                          typ
                                         in
                                      let uu____2676 =
                                        tts goal.FStar_Tactics_Types.context
                                          goal.FStar_Tactics_Types.goal_ty
                                         in
                                      let uu____2677 =
                                        tts goal.FStar_Tactics_Types.context
                                          goal.FStar_Tactics_Types.witness
                                         in
                                      fail4
                                        "%s : %s does not exactly solve the goal %s (witness = %s)"
                                        uu____2674 uu____2675 uu____2676
                                        uu____2677))))))
  
let (t_exact : Prims.bool -> FStar_Syntax_Syntax.term -> Prims.unit tac) =
  fun set_expected_typ1  ->
    fun tm  ->
      let uu____2688 =
        mlog
          (fun uu____2693  ->
             let uu____2694 = FStar_Syntax_Print.term_to_string tm  in
             FStar_Util.print1 "t_exact: tm = %s\n" uu____2694)
          (fun uu____2697  ->
             let uu____2698 =
               let uu____2705 = __exact_now set_expected_typ1 tm  in
               trytac' uu____2705  in
             bind uu____2698
               (fun uu___56_2714  ->
                  match uu___56_2714 with
                  | FStar_Util.Inr r -> ret ()
                  | FStar_Util.Inl e ->
                      let uu____2723 =
                        let uu____2730 =
                          let uu____2733 =
                            norm [FStar_Syntax_Embeddings.Delta]  in
                          bind uu____2733
                            (fun uu____2737  ->
                               bind refine_intro
                                 (fun uu____2739  ->
                                    __exact_now set_expected_typ1 tm))
                           in
                        trytac' uu____2730  in
                      bind uu____2723
                        (fun uu___55_2746  ->
                           match uu___55_2746 with
                           | FStar_Util.Inr r -> ret ()
                           | FStar_Util.Inl uu____2754 -> fail e)))
         in
      FStar_All.pipe_left (wrap_err "exact") uu____2688
  
let (uvar_free_in_goal :
  FStar_Syntax_Syntax.uvar -> FStar_Tactics_Types.goal -> Prims.bool) =
  fun u  ->
    fun g  ->
      if g.FStar_Tactics_Types.is_guard
      then false
      else
        (let free_uvars =
           let uu____2769 =
             let uu____2776 =
               FStar_Syntax_Free.uvars g.FStar_Tactics_Types.goal_ty  in
             FStar_Util.set_elements uu____2776  in
           FStar_List.map FStar_Pervasives_Native.fst uu____2769  in
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
          let uu____2836 = f x  in
          bind uu____2836
            (fun y  ->
               let uu____2844 = mapM f xs  in
               bind uu____2844 (fun ys  -> ret (y :: ys)))
  
exception NoUnif 
let (uu___is_NoUnif : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with | NoUnif  -> true | uu____2862 -> false
  
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
               (fun uu____2880  ->
                  let uu____2881 = FStar_Syntax_Print.term_to_string tm  in
                  FStar_Util.print1 ">>> Calling __exact(%s)\n" uu____2881)
               (fun uu____2884  ->
                  let uu____2885 =
                    let uu____2890 =
                      let uu____2893 = t_exact false tm  in
                      with_policy FStar_Tactics_Types.Force uu____2893  in
                    trytac uu____2890  in
                  bind uu____2885
                    (fun uu___57_2900  ->
                       match uu___57_2900 with
                       | FStar_Pervasives_Native.Some r -> ret ()
                       | FStar_Pervasives_Native.None  ->
                           mlog
                             (fun uu____2908  ->
                                let uu____2909 =
                                  FStar_Syntax_Print.term_to_string typ  in
                                FStar_Util.print1 ">>> typ = %s\n" uu____2909)
                             (fun uu____2912  ->
                                let uu____2913 =
                                  FStar_Syntax_Util.arrow_one typ  in
                                match uu____2913 with
                                | FStar_Pervasives_Native.None  ->
                                    FStar_Exn.raise NoUnif
                                | FStar_Pervasives_Native.Some ((bv,aq),c) ->
                                    mlog
                                      (fun uu____2945  ->
                                         let uu____2946 =
                                           FStar_Syntax_Print.binder_to_string
                                             (bv, aq)
                                            in
                                         FStar_Util.print1
                                           "__apply: pushing binder %s\n"
                                           uu____2946)
                                      (fun uu____2949  ->
                                         let uu____2950 =
                                           let uu____2951 =
                                             FStar_Syntax_Util.is_total_comp
                                               c
                                              in
                                           Prims.op_Negation uu____2951  in
                                         if uu____2950
                                         then
                                           fail "apply: not total codomain"
                                         else
                                           (let uu____2955 =
                                              new_uvar "apply"
                                                goal.FStar_Tactics_Types.context
                                                bv.FStar_Syntax_Syntax.sort
                                               in
                                            bind uu____2955
                                              (fun u  ->
                                                 let tm' =
                                                   FStar_Syntax_Syntax.mk_Tm_app
                                                     tm [(u, aq)]
                                                     FStar_Pervasives_Native.None
                                                     tm.FStar_Syntax_Syntax.pos
                                                    in
                                                 let typ' =
                                                   let uu____2975 =
                                                     comp_to_typ c  in
                                                   FStar_All.pipe_left
                                                     (FStar_Syntax_Subst.subst
                                                        [FStar_Syntax_Syntax.NT
                                                           (bv, u)])
                                                     uu____2975
                                                    in
                                                 let uu____2976 =
                                                   __apply uopt tm' typ'  in
                                                 bind uu____2976
                                                   (fun uu____2984  ->
                                                      let u1 =
                                                        bnorm
                                                          goal.FStar_Tactics_Types.context
                                                          u
                                                         in
                                                      let uu____2986 =
                                                        let uu____2987 =
                                                          let uu____2990 =
                                                            let uu____2991 =
                                                              FStar_Syntax_Util.head_and_args
                                                                u1
                                                               in
                                                            FStar_Pervasives_Native.fst
                                                              uu____2991
                                                             in
                                                          FStar_Syntax_Subst.compress
                                                            uu____2990
                                                           in
                                                        uu____2987.FStar_Syntax_Syntax.n
                                                         in
                                                      match uu____2986 with
                                                      | FStar_Syntax_Syntax.Tm_uvar
                                                          (uvar,uu____3019)
                                                          ->
                                                          bind get
                                                            (fun ps  ->
                                                               let uu____3047
                                                                 =
                                                                 uopt &&
                                                                   (uvar_free
                                                                    uvar ps)
                                                                  in
                                                               if uu____3047
                                                               then ret ()
                                                               else
                                                                 (let uu____3051
                                                                    =
                                                                    let uu____3054
                                                                    =
                                                                    let uu___85_3055
                                                                    = goal
                                                                     in
                                                                    let uu____3056
                                                                    =
                                                                    bnorm
                                                                    goal.FStar_Tactics_Types.context
                                                                    u1  in
                                                                    let uu____3057
                                                                    =
                                                                    bnorm
                                                                    goal.FStar_Tactics_Types.context
                                                                    bv.FStar_Syntax_Syntax.sort
                                                                     in
                                                                    {
                                                                    FStar_Tactics_Types.context
                                                                    =
                                                                    (uu___85_3055.FStar_Tactics_Types.context);
                                                                    FStar_Tactics_Types.witness
                                                                    =
                                                                    uu____3056;
                                                                    FStar_Tactics_Types.goal_ty
                                                                    =
                                                                    uu____3057;
                                                                    FStar_Tactics_Types.opts
                                                                    =
                                                                    (uu___85_3055.FStar_Tactics_Types.opts);
                                                                    FStar_Tactics_Types.is_guard
                                                                    = false
                                                                    }  in
                                                                    [uu____3054]
                                                                     in
                                                                  add_goals
                                                                    uu____3051))
                                                      | t -> ret ()))))))))
  
let try_unif : 'a . 'a tac -> 'a tac -> 'a tac =
  fun t  ->
    fun t'  -> mk_tac (fun ps  -> try run t ps with | NoUnif  -> run t' ps)
  
let (apply : Prims.bool -> FStar_Syntax_Syntax.term -> Prims.unit tac) =
  fun uopt  ->
    fun tm  ->
      let uu____3103 =
        mlog
          (fun uu____3108  ->
             let uu____3109 = FStar_Syntax_Print.term_to_string tm  in
             FStar_Util.print1 "apply: tm = %s\n" uu____3109)
          (fun uu____3111  ->
             bind cur_goal
               (fun goal  ->
                  let uu____3115 = __tc goal.FStar_Tactics_Types.context tm
                     in
                  bind uu____3115
                    (fun uu____3137  ->
                       match uu____3137 with
                       | (tm1,typ,guard) ->
                           let typ1 =
                             bnorm goal.FStar_Tactics_Types.context typ  in
                           let uu____3150 =
                             let uu____3153 =
                               let uu____3156 = __apply uopt tm1 typ1  in
                               bind uu____3156
                                 (fun uu____3160  ->
                                    proc_guard "apply guard"
                                      goal.FStar_Tactics_Types.context guard
                                      goal.FStar_Tactics_Types.opts)
                                in
                             focus uu____3153  in
                           let uu____3161 =
                             let uu____3164 =
                               tts goal.FStar_Tactics_Types.context tm1  in
                             let uu____3165 =
                               tts goal.FStar_Tactics_Types.context typ1  in
                             let uu____3166 =
                               tts goal.FStar_Tactics_Types.context
                                 goal.FStar_Tactics_Types.goal_ty
                                in
                             fail3
                               "Cannot instantiate %s (of type %s) to match goal (%s)"
                               uu____3164 uu____3165 uu____3166
                              in
                           try_unif uu____3150 uu____3161)))
         in
      FStar_All.pipe_left (wrap_err "apply") uu____3103
  
let (apply_lemma : FStar_Syntax_Syntax.term -> Prims.unit tac) =
  fun tm  ->
    let uu____3178 =
      let uu____3181 =
        mlog
          (fun uu____3186  ->
             let uu____3187 = FStar_Syntax_Print.term_to_string tm  in
             FStar_Util.print1 "apply_lemma: tm = %s\n" uu____3187)
          (fun uu____3190  ->
             let is_unit_t t =
               let uu____3195 =
                 let uu____3196 = FStar_Syntax_Subst.compress t  in
                 uu____3196.FStar_Syntax_Syntax.n  in
               match uu____3195 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.unit_lid
                   -> true
               | uu____3200 -> false  in
             bind cur_goal
               (fun goal  ->
                  let uu____3204 = __tc goal.FStar_Tactics_Types.context tm
                     in
                  bind uu____3204
                    (fun uu____3226  ->
                       match uu____3226 with
                       | (tm1,t,guard) ->
                           let uu____3238 =
                             FStar_Syntax_Util.arrow_formals_comp t  in
                           (match uu____3238 with
                            | (bs,comp) ->
                                if
                                  Prims.op_Negation
                                    (FStar_Syntax_Util.is_lemma_comp comp)
                                then fail "not a lemma"
                                else
                                  (let uu____3268 =
                                     FStar_List.fold_left
                                       (fun uu____3314  ->
                                          fun uu____3315  ->
                                            match (uu____3314, uu____3315)
                                            with
                                            | ((uvs,guard1,subst1),(b,aq)) ->
                                                let b_t =
                                                  FStar_Syntax_Subst.subst
                                                    subst1
                                                    b.FStar_Syntax_Syntax.sort
                                                   in
                                                let uu____3418 =
                                                  is_unit_t b_t  in
                                                if uu____3418
                                                then
                                                  (((FStar_Syntax_Util.exp_unit,
                                                      aq) :: uvs), guard1,
                                                    ((FStar_Syntax_Syntax.NT
                                                        (b,
                                                          FStar_Syntax_Util.exp_unit))
                                                    :: subst1))
                                                else
                                                  (let uu____3456 =
                                                     FStar_TypeChecker_Util.new_implicit_var
                                                       "apply_lemma"
                                                       (goal.FStar_Tactics_Types.goal_ty).FStar_Syntax_Syntax.pos
                                                       goal.FStar_Tactics_Types.context
                                                       b_t
                                                      in
                                                   match uu____3456 with
                                                   | (u,uu____3486,g_u) ->
                                                       let uu____3500 =
                                                         FStar_TypeChecker_Rel.conj_guard
                                                           guard1 g_u
                                                          in
                                                       (((u, aq) :: uvs),
                                                         uu____3500,
                                                         ((FStar_Syntax_Syntax.NT
                                                             (b, u)) ::
                                                         subst1))))
                                       ([], guard, []) bs
                                      in
                                   match uu____3268 with
                                   | (uvs,implicits,subst1) ->
                                       let uvs1 = FStar_List.rev uvs  in
                                       let comp1 =
                                         FStar_Syntax_Subst.subst_comp subst1
                                           comp
                                          in
                                       let uu____3570 =
                                         let uu____3579 =
                                           let uu____3588 =
                                             FStar_Syntax_Util.comp_to_comp_typ
                                               comp1
                                              in
                                           uu____3588.FStar_Syntax_Syntax.effect_args
                                            in
                                         match uu____3579 with
                                         | pre::post::uu____3599 ->
                                             ((FStar_Pervasives_Native.fst
                                                 pre),
                                               (FStar_Pervasives_Native.fst
                                                  post))
                                         | uu____3640 ->
                                             failwith
                                               "apply_lemma: impossible: not a lemma"
                                          in
                                       (match uu____3570 with
                                        | (pre,post) ->
                                            let post1 =
                                              let uu____3672 =
                                                let uu____3681 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    FStar_Syntax_Util.exp_unit
                                                   in
                                                [uu____3681]  in
                                              FStar_Syntax_Util.mk_app post
                                                uu____3672
                                               in
                                            let uu____3682 =
                                              let uu____3685 =
                                                FStar_Syntax_Util.mk_squash
                                                  FStar_Syntax_Syntax.U_zero
                                                  post1
                                                 in
                                              do_unify
                                                goal.FStar_Tactics_Types.context
                                                uu____3685
                                                goal.FStar_Tactics_Types.goal_ty
                                               in
                                            bind uu____3682
                                              (fun b  ->
                                                 if Prims.op_Negation b
                                                 then
                                                   let uu____3693 =
                                                     tts
                                                       goal.FStar_Tactics_Types.context
                                                       tm1
                                                      in
                                                   let uu____3694 =
                                                     let uu____3695 =
                                                       FStar_Syntax_Util.mk_squash
                                                         FStar_Syntax_Syntax.U_zero
                                                         post1
                                                        in
                                                     tts
                                                       goal.FStar_Tactics_Types.context
                                                       uu____3695
                                                      in
                                                   let uu____3696 =
                                                     tts
                                                       goal.FStar_Tactics_Types.context
                                                       goal.FStar_Tactics_Types.goal_ty
                                                      in
                                                   fail3
                                                     "Cannot instantiate lemma %s (with postcondition: %s) to match goal (%s)"
                                                     uu____3693 uu____3694
                                                     uu____3696
                                                 else
                                                   (let uu____3698 =
                                                      add_implicits
                                                        implicits.FStar_TypeChecker_Env.implicits
                                                       in
                                                    bind uu____3698
                                                      (fun uu____3703  ->
                                                         let uu____3704 =
                                                           solve goal
                                                             FStar_Syntax_Util.exp_unit
                                                            in
                                                         bind uu____3704
                                                           (fun uu____3712 
                                                              ->
                                                              let is_free_uvar
                                                                uv t1 =
                                                                let free_uvars
                                                                  =
                                                                  let uu____3723
                                                                    =
                                                                    let uu____3730
                                                                    =
                                                                    FStar_Syntax_Free.uvars
                                                                    t1  in
                                                                    FStar_Util.set_elements
                                                                    uu____3730
                                                                     in
                                                                  FStar_List.map
                                                                    FStar_Pervasives_Native.fst
                                                                    uu____3723
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
                                                                let uu____3771
                                                                  =
                                                                  FStar_Syntax_Util.head_and_args
                                                                    t1
                                                                   in
                                                                match uu____3771
                                                                with
                                                                | (hd1,uu____3787)
                                                                    ->
                                                                    (
                                                                    match 
                                                                    hd1.FStar_Syntax_Syntax.n
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Tm_uvar
                                                                    (uv,uu____3809)
                                                                    ->
                                                                    appears
                                                                    uv goals
                                                                    | 
                                                                    uu____3834
                                                                    -> false)
                                                                 in
                                                              let uu____3835
                                                                =
                                                                FStar_All.pipe_right
                                                                  implicits.FStar_TypeChecker_Env.implicits
                                                                  (mapM
                                                                    (fun
                                                                    uu____3907
                                                                     ->
                                                                    match uu____3907
                                                                    with
                                                                    | 
                                                                    (_msg,env,_uvar,term,typ,uu____3935)
                                                                    ->
                                                                    let uu____3936
                                                                    =
                                                                    FStar_Syntax_Util.head_and_args
                                                                    term  in
                                                                    (match uu____3936
                                                                    with
                                                                    | 
                                                                    (hd1,uu____3962)
                                                                    ->
                                                                    let uu____3983
                                                                    =
                                                                    let uu____3984
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    hd1  in
                                                                    uu____3984.FStar_Syntax_Syntax.n
                                                                     in
                                                                    (match uu____3983
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Tm_uvar
                                                                    uu____3997
                                                                    ->
                                                                    let uu____4014
                                                                    =
                                                                    let uu____4023
                                                                    =
                                                                    let uu____4026
                                                                    =
                                                                    let uu___88_4027
                                                                    = goal
                                                                     in
                                                                    let uu____4028
                                                                    =
                                                                    bnorm
                                                                    goal.FStar_Tactics_Types.context
                                                                    term  in
                                                                    let uu____4029
                                                                    =
                                                                    bnorm
                                                                    goal.FStar_Tactics_Types.context
                                                                    typ  in
                                                                    {
                                                                    FStar_Tactics_Types.context
                                                                    =
                                                                    (uu___88_4027.FStar_Tactics_Types.context);
                                                                    FStar_Tactics_Types.witness
                                                                    =
                                                                    uu____4028;
                                                                    FStar_Tactics_Types.goal_ty
                                                                    =
                                                                    uu____4029;
                                                                    FStar_Tactics_Types.opts
                                                                    =
                                                                    (uu___88_4027.FStar_Tactics_Types.opts);
                                                                    FStar_Tactics_Types.is_guard
                                                                    =
                                                                    (uu___88_4027.FStar_Tactics_Types.is_guard)
                                                                    }  in
                                                                    [uu____4026]
                                                                     in
                                                                    (uu____4023,
                                                                    [])  in
                                                                    ret
                                                                    uu____4014
                                                                    | 
                                                                    uu____4042
                                                                    ->
                                                                    let g_typ
                                                                    =
                                                                    let uu____4044
                                                                    =
                                                                    FStar_Options.__temp_fast_implicits
                                                                    ()  in
                                                                    if
                                                                    uu____4044
                                                                    then
                                                                    FStar_TypeChecker_TcTerm.check_type_of_well_typed_term
                                                                    false env
                                                                    term typ
                                                                    else
                                                                    (let term1
                                                                    =
                                                                    bnorm env
                                                                    term  in
                                                                    let uu____4047
                                                                    =
                                                                    let uu____4054
                                                                    =
                                                                    FStar_TypeChecker_Env.set_expected_typ
                                                                    env typ
                                                                     in
                                                                    env.FStar_TypeChecker_Env.type_of
                                                                    uu____4054
                                                                    term1  in
                                                                    match uu____4047
                                                                    with
                                                                    | 
                                                                    (uu____4055,uu____4056,g_typ)
                                                                    -> g_typ)
                                                                     in
                                                                    let uu____4058
                                                                    =
                                                                    goal_from_guard
                                                                    "apply_lemma solved arg"
                                                                    goal.FStar_Tactics_Types.context
                                                                    g_typ
                                                                    goal.FStar_Tactics_Types.opts
                                                                     in
                                                                    bind
                                                                    uu____4058
                                                                    (fun
                                                                    uu___58_4074
                                                                     ->
                                                                    match uu___58_4074
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
                                                              bind uu____3835
                                                                (fun goals_ 
                                                                   ->
                                                                   let sub_goals
                                                                    =
                                                                    let uu____4142
                                                                    =
                                                                    FStar_List.map
                                                                    FStar_Pervasives_Native.fst
                                                                    goals_
                                                                     in
                                                                    FStar_List.flatten
                                                                    uu____4142
                                                                     in
                                                                   let smt_goals
                                                                    =
                                                                    let uu____4164
                                                                    =
                                                                    FStar_List.map
                                                                    FStar_Pervasives_Native.snd
                                                                    goals_
                                                                     in
                                                                    FStar_List.flatten
                                                                    uu____4164
                                                                     in
                                                                   let rec filter'
                                                                    a f xs =
                                                                    match xs
                                                                    with
                                                                    | 
                                                                    [] -> []
                                                                    | 
                                                                    x::xs1 ->
                                                                    let uu____4219
                                                                    = f x xs1
                                                                     in
                                                                    if
                                                                    uu____4219
                                                                    then
                                                                    let uu____4222
                                                                    =
                                                                    filter'
                                                                    () f xs1
                                                                     in x ::
                                                                    uu____4222
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
                                                                    let uu____4236
                                                                    =
                                                                    checkone
                                                                    g.FStar_Tactics_Types.witness
                                                                    goals  in
                                                                    Prims.op_Negation
                                                                    uu____4236))
                                                                    a438 a439)
                                                                    (Obj.magic
                                                                    sub_goals))
                                                                     in
                                                                   let uu____4237
                                                                    =
                                                                    proc_guard
                                                                    "apply_lemma guard"
                                                                    goal.FStar_Tactics_Types.context
                                                                    guard
                                                                    goal.FStar_Tactics_Types.opts
                                                                     in
                                                                   bind
                                                                    uu____4237
                                                                    (fun
                                                                    uu____4242
                                                                     ->
                                                                    let uu____4243
                                                                    =
                                                                    let uu____4246
                                                                    =
                                                                    let uu____4247
                                                                    =
                                                                    let uu____4248
                                                                    =
                                                                    FStar_Syntax_Util.mk_squash
                                                                    FStar_Syntax_Syntax.U_zero
                                                                    pre  in
                                                                    istrivial
                                                                    goal.FStar_Tactics_Types.context
                                                                    uu____4248
                                                                     in
                                                                    Prims.op_Negation
                                                                    uu____4247
                                                                     in
                                                                    if
                                                                    uu____4246
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
                                                                    uu____4243
                                                                    (fun
                                                                    uu____4254
                                                                     ->
                                                                    let uu____4255
                                                                    =
                                                                    add_smt_goals
                                                                    smt_goals
                                                                     in
                                                                    bind
                                                                    uu____4255
                                                                    (fun
                                                                    uu____4259
                                                                     ->
                                                                    add_goals
                                                                    sub_goals1))))))))))))))
         in
      focus uu____3181  in
    FStar_All.pipe_left (wrap_err "apply_lemma") uu____3178
  
let (destruct_eq' :
  FStar_Syntax_Syntax.typ ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun typ  ->
    let uu____4279 = FStar_Syntax_Util.destruct_typ_as_formula typ  in
    match uu____4279 with
    | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn
        (l,uu____4289::(e1,uu____4291)::(e2,uu____4293)::[])) when
        FStar_Ident.lid_equals l FStar_Parser_Const.eq2_lid ->
        FStar_Pervasives_Native.Some (e1, e2)
    | uu____4352 -> FStar_Pervasives_Native.None
  
let (destruct_eq :
  FStar_Syntax_Syntax.typ ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun typ  ->
    let uu____4374 = destruct_eq' typ  in
    match uu____4374 with
    | FStar_Pervasives_Native.Some t -> FStar_Pervasives_Native.Some t
    | FStar_Pervasives_Native.None  ->
        let uu____4404 = FStar_Syntax_Util.un_squash typ  in
        (match uu____4404 with
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
        let uu____4460 = FStar_TypeChecker_Env.pop_bv e1  in
        match uu____4460 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (bv',e') ->
            if FStar_Syntax_Syntax.bv_eq bvar bv'
            then FStar_Pervasives_Native.Some (e', [])
            else
              (let uu____4508 = aux e'  in
               FStar_Util.map_opt uu____4508
                 (fun uu____4532  ->
                    match uu____4532 with | (e'',bvs) -> (e'', (bv' :: bvs))))
         in
      let uu____4553 = aux e  in
      FStar_Util.map_opt uu____4553
        (fun uu____4577  ->
           match uu____4577 with | (e',bvs) -> (e', (FStar_List.rev bvs)))
  
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
          let uu____4632 = split_env b1 g.FStar_Tactics_Types.context  in
          FStar_Util.map_opt uu____4632
            (fun uu____4656  ->
               match uu____4656 with
               | (e0,bvs) ->
                   let s1 bv =
                     let uu___89_4673 = bv  in
                     let uu____4674 =
                       FStar_Syntax_Subst.subst s bv.FStar_Syntax_Syntax.sort
                        in
                     {
                       FStar_Syntax_Syntax.ppname =
                         (uu___89_4673.FStar_Syntax_Syntax.ppname);
                       FStar_Syntax_Syntax.index =
                         (uu___89_4673.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort = uu____4674
                     }  in
                   let bvs1 = FStar_List.map s1 bvs  in
                   let c = push_bvs e0 (b2 :: bvs1)  in
                   let w =
                     FStar_Syntax_Subst.subst s g.FStar_Tactics_Types.witness
                      in
                   let t =
                     FStar_Syntax_Subst.subst s g.FStar_Tactics_Types.goal_ty
                      in
                   let uu___90_4683 = g  in
                   {
                     FStar_Tactics_Types.context = c;
                     FStar_Tactics_Types.witness = w;
                     FStar_Tactics_Types.goal_ty = t;
                     FStar_Tactics_Types.opts =
                       (uu___90_4683.FStar_Tactics_Types.opts);
                     FStar_Tactics_Types.is_guard =
                       (uu___90_4683.FStar_Tactics_Types.is_guard)
                   })
  
let (rewrite : FStar_Syntax_Syntax.binder -> Prims.unit tac) =
  fun h  ->
    bind cur_goal
      (fun goal  ->
         let uu____4696 = h  in
         match uu____4696 with
         | (bv,uu____4700) ->
             mlog
               (fun uu____4704  ->
                  let uu____4705 = FStar_Syntax_Print.bv_to_string bv  in
                  let uu____4706 =
                    tts goal.FStar_Tactics_Types.context
                      bv.FStar_Syntax_Syntax.sort
                     in
                  FStar_Util.print2 "+++Rewrite %s : %s\n" uu____4705
                    uu____4706)
               (fun uu____4709  ->
                  let uu____4710 =
                    split_env bv goal.FStar_Tactics_Types.context  in
                  match uu____4710 with
                  | FStar_Pervasives_Native.None  ->
                      fail "rewrite: binder not found in environment"
                  | FStar_Pervasives_Native.Some (e0,bvs) ->
                      let uu____4739 =
                        destruct_eq bv.FStar_Syntax_Syntax.sort  in
                      (match uu____4739 with
                       | FStar_Pervasives_Native.Some (x,e) ->
                           let uu____4754 =
                             let uu____4755 = FStar_Syntax_Subst.compress x
                                in
                             uu____4755.FStar_Syntax_Syntax.n  in
                           (match uu____4754 with
                            | FStar_Syntax_Syntax.Tm_name x1 ->
                                let s = [FStar_Syntax_Syntax.NT (x1, e)]  in
                                let s1 bv1 =
                                  let uu___91_4768 = bv1  in
                                  let uu____4769 =
                                    FStar_Syntax_Subst.subst s
                                      bv1.FStar_Syntax_Syntax.sort
                                     in
                                  {
                                    FStar_Syntax_Syntax.ppname =
                                      (uu___91_4768.FStar_Syntax_Syntax.ppname);
                                    FStar_Syntax_Syntax.index =
                                      (uu___91_4768.FStar_Syntax_Syntax.index);
                                    FStar_Syntax_Syntax.sort = uu____4769
                                  }  in
                                let bvs1 = FStar_List.map s1 bvs  in
                                let uu____4775 =
                                  let uu___92_4776 = goal  in
                                  let uu____4777 = push_bvs e0 (bv :: bvs1)
                                     in
                                  let uu____4778 =
                                    FStar_Syntax_Subst.subst s
                                      goal.FStar_Tactics_Types.witness
                                     in
                                  let uu____4779 =
                                    FStar_Syntax_Subst.subst s
                                      goal.FStar_Tactics_Types.goal_ty
                                     in
                                  {
                                    FStar_Tactics_Types.context = uu____4777;
                                    FStar_Tactics_Types.witness = uu____4778;
                                    FStar_Tactics_Types.goal_ty = uu____4779;
                                    FStar_Tactics_Types.opts =
                                      (uu___92_4776.FStar_Tactics_Types.opts);
                                    FStar_Tactics_Types.is_guard =
                                      (uu___92_4776.FStar_Tactics_Types.is_guard)
                                  }  in
                                replace_cur uu____4775
                            | uu____4780 ->
                                fail
                                  "rewrite: Not an equality hypothesis with a variable on the LHS")
                       | uu____4781 ->
                           fail "rewrite: Not an equality hypothesis")))
  
let (rename_to :
  FStar_Syntax_Syntax.binder -> Prims.string -> Prims.unit tac) =
  fun b  ->
    fun s  ->
      bind cur_goal
        (fun goal  ->
           let uu____4806 = b  in
           match uu____4806 with
           | (bv,uu____4810) ->
               let bv' =
                 FStar_Syntax_Syntax.freshen_bv
                   (let uu___93_4814 = bv  in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (FStar_Ident.mk_ident
                           (s,
                             ((bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange)));
                      FStar_Syntax_Syntax.index =
                        (uu___93_4814.FStar_Syntax_Syntax.index);
                      FStar_Syntax_Syntax.sort =
                        (uu___93_4814.FStar_Syntax_Syntax.sort)
                    })
                  in
               let s1 =
                 let uu____4818 =
                   let uu____4819 =
                     let uu____4826 = FStar_Syntax_Syntax.bv_to_name bv'  in
                     (bv, uu____4826)  in
                   FStar_Syntax_Syntax.NT uu____4819  in
                 [uu____4818]  in
               let uu____4827 = subst_goal bv bv' s1 goal  in
               (match uu____4827 with
                | FStar_Pervasives_Native.None  ->
                    fail "rename_to: binder not found in environment"
                | FStar_Pervasives_Native.Some goal1 -> replace_cur goal1))
  
let (binder_retype : FStar_Syntax_Syntax.binder -> Prims.unit tac) =
  fun b  ->
    bind cur_goal
      (fun goal  ->
         let uu____4846 = b  in
         match uu____4846 with
         | (bv,uu____4850) ->
             let uu____4851 = split_env bv goal.FStar_Tactics_Types.context
                in
             (match uu____4851 with
              | FStar_Pervasives_Native.None  ->
                  fail "binder_retype: binder is not present in environment"
              | FStar_Pervasives_Native.Some (e0,bvs) ->
                  let uu____4880 = FStar_Syntax_Util.type_u ()  in
                  (match uu____4880 with
                   | (ty,u) ->
                       let uu____4889 = new_uvar "binder_retype" e0 ty  in
                       bind uu____4889
                         (fun t'  ->
                            let bv'' =
                              let uu___94_4899 = bv  in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___94_4899.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___94_4899.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = t'
                              }  in
                            let s =
                              let uu____4903 =
                                let uu____4904 =
                                  let uu____4911 =
                                    FStar_Syntax_Syntax.bv_to_name bv''  in
                                  (bv, uu____4911)  in
                                FStar_Syntax_Syntax.NT uu____4904  in
                              [uu____4903]  in
                            let bvs1 =
                              FStar_List.map
                                (fun b1  ->
                                   let uu___95_4919 = b1  in
                                   let uu____4920 =
                                     FStar_Syntax_Subst.subst s
                                       b1.FStar_Syntax_Syntax.sort
                                      in
                                   {
                                     FStar_Syntax_Syntax.ppname =
                                       (uu___95_4919.FStar_Syntax_Syntax.ppname);
                                     FStar_Syntax_Syntax.index =
                                       (uu___95_4919.FStar_Syntax_Syntax.index);
                                     FStar_Syntax_Syntax.sort = uu____4920
                                   }) bvs
                               in
                            let env' = push_bvs e0 (bv'' :: bvs1)  in
                            bind dismiss
                              (fun uu____4926  ->
                                 let uu____4927 =
                                   let uu____4930 =
                                     let uu____4933 =
                                       let uu___96_4934 = goal  in
                                       let uu____4935 =
                                         FStar_Syntax_Subst.subst s
                                           goal.FStar_Tactics_Types.witness
                                          in
                                       let uu____4936 =
                                         FStar_Syntax_Subst.subst s
                                           goal.FStar_Tactics_Types.goal_ty
                                          in
                                       {
                                         FStar_Tactics_Types.context = env';
                                         FStar_Tactics_Types.witness =
                                           uu____4935;
                                         FStar_Tactics_Types.goal_ty =
                                           uu____4936;
                                         FStar_Tactics_Types.opts =
                                           (uu___96_4934.FStar_Tactics_Types.opts);
                                         FStar_Tactics_Types.is_guard =
                                           (uu___96_4934.FStar_Tactics_Types.is_guard)
                                       }  in
                                     [uu____4933]  in
                                   add_goals uu____4930  in
                                 bind uu____4927
                                   (fun uu____4939  ->
                                      let uu____4940 =
                                        FStar_Syntax_Util.mk_eq2
                                          (FStar_Syntax_Syntax.U_succ u) ty
                                          bv.FStar_Syntax_Syntax.sort t'
                                         in
                                      add_irrelevant_goal
                                        "binder_retype equation" e0
                                        uu____4940
                                        goal.FStar_Tactics_Types.opts))))))
  
let (norm_binder_type :
  FStar_Syntax_Embeddings.norm_step Prims.list ->
    FStar_Syntax_Syntax.binder -> Prims.unit tac)
  =
  fun s  ->
    fun b  ->
      bind cur_goal
        (fun goal  ->
           let uu____4961 = b  in
           match uu____4961 with
           | (bv,uu____4965) ->
               let uu____4966 = split_env bv goal.FStar_Tactics_Types.context
                  in
               (match uu____4966 with
                | FStar_Pervasives_Native.None  ->
                    fail
                      "binder_retype: binder is not present in environment"
                | FStar_Pervasives_Native.Some (e0,bvs) ->
                    let steps =
                      let uu____4998 =
                        FStar_TypeChecker_Normalize.tr_norm_steps s  in
                      FStar_List.append
                        [FStar_TypeChecker_Normalize.Reify;
                        FStar_TypeChecker_Normalize.UnfoldTac] uu____4998
                       in
                    let sort' =
                      normalize steps e0 bv.FStar_Syntax_Syntax.sort  in
                    let bv' =
                      let uu___97_5003 = bv  in
                      {
                        FStar_Syntax_Syntax.ppname =
                          (uu___97_5003.FStar_Syntax_Syntax.ppname);
                        FStar_Syntax_Syntax.index =
                          (uu___97_5003.FStar_Syntax_Syntax.index);
                        FStar_Syntax_Syntax.sort = sort'
                      }  in
                    let env' = push_bvs e0 (bv' :: bvs)  in
                    replace_cur
                      (let uu___98_5007 = goal  in
                       {
                         FStar_Tactics_Types.context = env';
                         FStar_Tactics_Types.witness =
                           (uu___98_5007.FStar_Tactics_Types.witness);
                         FStar_Tactics_Types.goal_ty =
                           (uu___98_5007.FStar_Tactics_Types.goal_ty);
                         FStar_Tactics_Types.opts =
                           (uu___98_5007.FStar_Tactics_Types.opts);
                         FStar_Tactics_Types.is_guard =
                           (uu___98_5007.FStar_Tactics_Types.is_guard)
                       })))
  
let (revert : Prims.unit tac) =
  bind cur_goal
    (fun goal  ->
       let uu____5015 =
         FStar_TypeChecker_Env.pop_bv goal.FStar_Tactics_Types.context  in
       match uu____5015 with
       | FStar_Pervasives_Native.None  -> fail "Cannot revert; empty context"
       | FStar_Pervasives_Native.Some (x,env') ->
           let typ' =
             let uu____5037 =
               FStar_Syntax_Syntax.mk_Total goal.FStar_Tactics_Types.goal_ty
                in
             FStar_Syntax_Util.arrow [(x, FStar_Pervasives_Native.None)]
               uu____5037
              in
           let w' =
             FStar_Syntax_Util.abs [(x, FStar_Pervasives_Native.None)]
               goal.FStar_Tactics_Types.witness FStar_Pervasives_Native.None
              in
           replace_cur
             (let uu___99_5071 = goal  in
              {
                FStar_Tactics_Types.context = env';
                FStar_Tactics_Types.witness = w';
                FStar_Tactics_Types.goal_ty = typ';
                FStar_Tactics_Types.opts =
                  (uu___99_5071.FStar_Tactics_Types.opts);
                FStar_Tactics_Types.is_guard =
                  (uu___99_5071.FStar_Tactics_Types.is_guard)
              }))
  
let (free_in :
  FStar_Syntax_Syntax.bv -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun bv  ->
    fun t  ->
      let uu____5078 = FStar_Syntax_Free.names t  in
      FStar_Util.set_mem bv uu____5078
  
let rec (clear : FStar_Syntax_Syntax.binder -> Prims.unit tac) =
  fun b  ->
    let bv = FStar_Pervasives_Native.fst b  in
    bind cur_goal
      (fun goal  ->
         mlog
           (fun uu____5094  ->
              let uu____5095 = FStar_Syntax_Print.binder_to_string b  in
              let uu____5096 =
                let uu____5097 =
                  let uu____5098 =
                    FStar_TypeChecker_Env.all_binders
                      goal.FStar_Tactics_Types.context
                     in
                  FStar_All.pipe_right uu____5098 FStar_List.length  in
                FStar_All.pipe_right uu____5097 FStar_Util.string_of_int  in
              FStar_Util.print2 "Clear of (%s), env has %s binders\n"
                uu____5095 uu____5096)
           (fun uu____5109  ->
              let uu____5110 = split_env bv goal.FStar_Tactics_Types.context
                 in
              match uu____5110 with
              | FStar_Pervasives_Native.None  ->
                  fail "Cannot clear; binder not in environment"
              | FStar_Pervasives_Native.Some (e',bvs) ->
                  let rec check bvs1 =
                    match bvs1 with
                    | [] -> ret ()
                    | bv'::bvs2 ->
                        let uu____5155 =
                          free_in bv bv'.FStar_Syntax_Syntax.sort  in
                        if uu____5155
                        then
                          let uu____5158 =
                            let uu____5159 =
                              FStar_Syntax_Print.bv_to_string bv'  in
                            FStar_Util.format1
                              "Cannot clear; binder present in the type of %s"
                              uu____5159
                             in
                          fail uu____5158
                        else check bvs2
                     in
                  let uu____5161 =
                    free_in bv goal.FStar_Tactics_Types.goal_ty  in
                  if uu____5161
                  then fail "Cannot clear; binder present in goal"
                  else
                    (let uu____5165 = check bvs  in
                     bind uu____5165
                       (fun uu____5171  ->
                          let env' = push_bvs e' bvs  in
                          let uu____5173 =
                            new_uvar "clear.witness" env'
                              goal.FStar_Tactics_Types.goal_ty
                             in
                          bind uu____5173
                            (fun ut  ->
                               let uu____5179 =
                                 do_unify goal.FStar_Tactics_Types.context
                                   goal.FStar_Tactics_Types.witness ut
                                  in
                               bind uu____5179
                                 (fun b1  ->
                                    if b1
                                    then
                                      replace_cur
                                        (let uu___100_5188 = goal  in
                                         {
                                           FStar_Tactics_Types.context = env';
                                           FStar_Tactics_Types.witness = ut;
                                           FStar_Tactics_Types.goal_ty =
                                             (uu___100_5188.FStar_Tactics_Types.goal_ty);
                                           FStar_Tactics_Types.opts =
                                             (uu___100_5188.FStar_Tactics_Types.opts);
                                           FStar_Tactics_Types.is_guard =
                                             (uu___100_5188.FStar_Tactics_Types.is_guard)
                                         })
                                    else
                                      fail
                                        "Cannot clear; binder appears in witness"))))))
  
let (clear_top : Prims.unit tac) =
  bind cur_goal
    (fun goal  ->
       let uu____5197 =
         FStar_TypeChecker_Env.pop_bv goal.FStar_Tactics_Types.context  in
       match uu____5197 with
       | FStar_Pervasives_Native.None  -> fail "Cannot clear; empty context"
       | FStar_Pervasives_Native.Some (x,uu____5211) ->
           let uu____5216 = FStar_Syntax_Syntax.mk_binder x  in
           clear uu____5216)
  
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
           let uu___101_5232 = g  in
           {
             FStar_Tactics_Types.context = ctx';
             FStar_Tactics_Types.witness =
               (uu___101_5232.FStar_Tactics_Types.witness);
             FStar_Tactics_Types.goal_ty =
               (uu___101_5232.FStar_Tactics_Types.goal_ty);
             FStar_Tactics_Types.opts =
               (uu___101_5232.FStar_Tactics_Types.opts);
             FStar_Tactics_Types.is_guard =
               (uu___101_5232.FStar_Tactics_Types.is_guard)
           }  in
         bind dismiss (fun uu____5234  -> add_goals [g']))
  
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
           let uu___102_5250 = g  in
           {
             FStar_Tactics_Types.context = ctx';
             FStar_Tactics_Types.witness =
               (uu___102_5250.FStar_Tactics_Types.witness);
             FStar_Tactics_Types.goal_ty =
               (uu___102_5250.FStar_Tactics_Types.goal_ty);
             FStar_Tactics_Types.opts =
               (uu___102_5250.FStar_Tactics_Types.opts);
             FStar_Tactics_Types.is_guard =
               (uu___102_5250.FStar_Tactics_Types.is_guard)
           }  in
         bind dismiss (fun uu____5252  -> add_goals [g']))
  
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
            let uu____5284 = FStar_Syntax_Subst.compress t  in
            uu____5284.FStar_Syntax_Syntax.n  in
          let uu____5287 =
            if d = FStar_Tactics_Types.TopDown
            then
              f env
                (let uu___104_5293 = t  in
                 {
                   FStar_Syntax_Syntax.n = tn;
                   FStar_Syntax_Syntax.pos =
                     (uu___104_5293.FStar_Syntax_Syntax.pos);
                   FStar_Syntax_Syntax.vars =
                     (uu___104_5293.FStar_Syntax_Syntax.vars)
                 })
            else ret t  in
          bind uu____5287
            (fun t1  ->
               let tn1 =
                 let uu____5301 =
                   let uu____5302 = FStar_Syntax_Subst.compress t1  in
                   uu____5302.FStar_Syntax_Syntax.n  in
                 match uu____5301 with
                 | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
                     let ff = tac_fold_env d f env  in
                     let uu____5334 = ff hd1  in
                     bind uu____5334
                       (fun hd2  ->
                          let fa uu____5354 =
                            match uu____5354 with
                            | (a,q) ->
                                let uu____5367 = ff a  in
                                bind uu____5367 (fun a1  -> ret (a1, q))
                             in
                          let uu____5380 = mapM fa args  in
                          bind uu____5380
                            (fun args1  ->
                               ret (FStar_Syntax_Syntax.Tm_app (hd2, args1))))
                 | FStar_Syntax_Syntax.Tm_abs (bs,t2,k) ->
                     let uu____5440 = FStar_Syntax_Subst.open_term bs t2  in
                     (match uu____5440 with
                      | (bs1,t') ->
                          let uu____5449 =
                            let uu____5452 =
                              FStar_TypeChecker_Env.push_binders env bs1  in
                            tac_fold_env d f uu____5452 t'  in
                          bind uu____5449
                            (fun t''  ->
                               let uu____5456 =
                                 let uu____5457 =
                                   let uu____5474 =
                                     FStar_Syntax_Subst.close_binders bs1  in
                                   let uu____5475 =
                                     FStar_Syntax_Subst.close bs1 t''  in
                                   (uu____5474, uu____5475, k)  in
                                 FStar_Syntax_Syntax.Tm_abs uu____5457  in
                               ret uu____5456))
                 | FStar_Syntax_Syntax.Tm_arrow (bs,k) -> ret tn
                 | uu____5496 -> ret tn  in
               bind tn1
                 (fun tn2  ->
                    let t' =
                      let uu___103_5503 = t1  in
                      {
                        FStar_Syntax_Syntax.n = tn2;
                        FStar_Syntax_Syntax.pos =
                          (uu___103_5503.FStar_Syntax_Syntax.pos);
                        FStar_Syntax_Syntax.vars =
                          (uu___103_5503.FStar_Syntax_Syntax.vars)
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
            let uu____5532 = FStar_TypeChecker_TcTerm.tc_term env t  in
            match uu____5532 with
            | (t1,lcomp,g) ->
                let uu____5544 =
                  (let uu____5547 =
                     FStar_Syntax_Util.is_pure_or_ghost_lcomp lcomp  in
                   Prims.op_Negation uu____5547) ||
                    (let uu____5549 = FStar_TypeChecker_Rel.is_trivial g  in
                     Prims.op_Negation uu____5549)
                   in
                if uu____5544
                then ret t1
                else
                  (let rewrite_eq =
                     let typ = lcomp.FStar_Syntax_Syntax.res_typ  in
                     let uu____5559 = new_uvar "pointwise_rec" env typ  in
                     bind uu____5559
                       (fun ut  ->
                          log ps
                            (fun uu____5570  ->
                               let uu____5571 =
                                 FStar_Syntax_Print.term_to_string t1  in
                               let uu____5572 =
                                 FStar_Syntax_Print.term_to_string ut  in
                               FStar_Util.print2
                                 "Pointwise_rec: making equality\n\t%s ==\n\t%s\n"
                                 uu____5571 uu____5572);
                          (let uu____5573 =
                             let uu____5576 =
                               let uu____5577 =
                                 FStar_TypeChecker_TcTerm.universe_of env typ
                                  in
                               FStar_Syntax_Util.mk_eq2 uu____5577 typ t1 ut
                                in
                             add_irrelevant_goal "pointwise_rec equation" env
                               uu____5576 opts
                              in
                           bind uu____5573
                             (fun uu____5580  ->
                                let uu____5581 =
                                  bind tau
                                    (fun uu____5587  ->
                                       let ut1 =
                                         FStar_TypeChecker_Normalize.reduce_uvar_solutions
                                           env ut
                                          in
                                       log ps
                                         (fun uu____5593  ->
                                            let uu____5594 =
                                              FStar_Syntax_Print.term_to_string
                                                t1
                                               in
                                            let uu____5595 =
                                              FStar_Syntax_Print.term_to_string
                                                ut1
                                               in
                                            FStar_Util.print2
                                              "Pointwise_rec: succeeded rewriting\n\t%s to\n\t%s\n"
                                              uu____5594 uu____5595);
                                       ret ut1)
                                   in
                                focus uu____5581)))
                      in
                   let uu____5596 = trytac' rewrite_eq  in
                   bind uu____5596
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
          let uu____5744 = FStar_Syntax_Subst.compress t  in
          maybe_continue ctrl uu____5744
            (fun t1  ->
               let uu____5748 =
                 f env
                   (let uu___107_5757 = t1  in
                    {
                      FStar_Syntax_Syntax.n = (t1.FStar_Syntax_Syntax.n);
                      FStar_Syntax_Syntax.pos =
                        (uu___107_5757.FStar_Syntax_Syntax.pos);
                      FStar_Syntax_Syntax.vars =
                        (uu___107_5757.FStar_Syntax_Syntax.vars)
                    })
                  in
               bind uu____5748
                 (fun uu____5769  ->
                    match uu____5769 with
                    | (t2,ctrl1) ->
                        maybe_continue ctrl1 t2
                          (fun t3  ->
                             let uu____5788 =
                               let uu____5789 =
                                 FStar_Syntax_Subst.compress t3  in
                               uu____5789.FStar_Syntax_Syntax.n  in
                             match uu____5788 with
                             | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
                                 let uu____5822 =
                                   ctrl_tac_fold f env ctrl1 hd1  in
                                 bind uu____5822
                                   (fun uu____5847  ->
                                      match uu____5847 with
                                      | (hd2,ctrl2) ->
                                          let ctrl3 = keep_going ctrl2  in
                                          let uu____5863 =
                                            ctrl_tac_fold_args f env ctrl3
                                              args
                                             in
                                          bind uu____5863
                                            (fun uu____5890  ->
                                               match uu____5890 with
                                               | (args1,ctrl4) ->
                                                   ret
                                                     ((let uu___105_5920 = t3
                                                          in
                                                       {
                                                         FStar_Syntax_Syntax.n
                                                           =
                                                           (FStar_Syntax_Syntax.Tm_app
                                                              (hd2, args1));
                                                         FStar_Syntax_Syntax.pos
                                                           =
                                                           (uu___105_5920.FStar_Syntax_Syntax.pos);
                                                         FStar_Syntax_Syntax.vars
                                                           =
                                                           (uu___105_5920.FStar_Syntax_Syntax.vars)
                                                       }), ctrl4)))
                             | FStar_Syntax_Syntax.Tm_abs (bs,t4,k) ->
                                 let uu____5946 =
                                   FStar_Syntax_Subst.open_term bs t4  in
                                 (match uu____5946 with
                                  | (bs1,t') ->
                                      let uu____5961 =
                                        let uu____5968 =
                                          FStar_TypeChecker_Env.push_binders
                                            env bs1
                                           in
                                        ctrl_tac_fold f uu____5968 ctrl1 t'
                                         in
                                      bind uu____5961
                                        (fun uu____5986  ->
                                           match uu____5986 with
                                           | (t'',ctrl2) ->
                                               let uu____6001 =
                                                 let uu____6008 =
                                                   let uu___106_6011 = t4  in
                                                   let uu____6014 =
                                                     let uu____6015 =
                                                       let uu____6032 =
                                                         FStar_Syntax_Subst.close_binders
                                                           bs1
                                                          in
                                                       let uu____6033 =
                                                         FStar_Syntax_Subst.close
                                                           bs1 t''
                                                          in
                                                       (uu____6032,
                                                         uu____6033, k)
                                                        in
                                                     FStar_Syntax_Syntax.Tm_abs
                                                       uu____6015
                                                      in
                                                   {
                                                     FStar_Syntax_Syntax.n =
                                                       uu____6014;
                                                     FStar_Syntax_Syntax.pos
                                                       =
                                                       (uu___106_6011.FStar_Syntax_Syntax.pos);
                                                     FStar_Syntax_Syntax.vars
                                                       =
                                                       (uu___106_6011.FStar_Syntax_Syntax.vars)
                                                   }  in
                                                 (uu____6008, ctrl2)  in
                                               ret uu____6001))
                             | FStar_Syntax_Syntax.Tm_arrow (bs,k) ->
                                 ret (t3, ctrl1)
                             | uu____6066 -> ret (t3, ctrl1))))

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
              let uu____6117 = ctrl_tac_fold f env ctrl t  in
              bind uu____6117
                (fun uu____6145  ->
                   match uu____6145 with
                   | (t1,ctrl1) ->
                       let uu____6164 = ctrl_tac_fold_args f env ctrl1 ts1
                          in
                       bind uu____6164
                         (fun uu____6195  ->
                            match uu____6195 with
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
              let uu____6279 =
                let uu____6286 =
                  add_irrelevant_goal "dummy" env FStar_Syntax_Util.t_true
                    opts
                   in
                bind uu____6286
                  (fun uu____6295  ->
                     let uu____6296 = ctrl t1  in
                     bind uu____6296
                       (fun res  -> bind trivial (fun uu____6323  -> ret res)))
                 in
              bind uu____6279
                (fun uu____6339  ->
                   match uu____6339 with
                   | (should_rewrite,ctrl1) ->
                       if Prims.op_Negation should_rewrite
                       then ret (t1, ctrl1)
                       else
                         (let uu____6363 =
                            FStar_TypeChecker_TcTerm.tc_term env t1  in
                          match uu____6363 with
                          | (t2,lcomp,g) ->
                              let uu____6379 =
                                (let uu____6382 =
                                   FStar_Syntax_Util.is_pure_or_ghost_lcomp
                                     lcomp
                                    in
                                 Prims.op_Negation uu____6382) ||
                                  (let uu____6384 =
                                     FStar_TypeChecker_Rel.is_trivial g  in
                                   Prims.op_Negation uu____6384)
                                 in
                              if uu____6379
                              then ret (t2, globalStop)
                              else
                                (let typ = lcomp.FStar_Syntax_Syntax.res_typ
                                    in
                                 let uu____6399 =
                                   new_uvar "pointwise_rec" env typ  in
                                 bind uu____6399
                                   (fun ut  ->
                                      log ps
                                        (fun uu____6414  ->
                                           let uu____6415 =
                                             FStar_Syntax_Print.term_to_string
                                               t2
                                              in
                                           let uu____6416 =
                                             FStar_Syntax_Print.term_to_string
                                               ut
                                              in
                                           FStar_Util.print2
                                             "Pointwise_rec: making equality\n\t%s ==\n\t%s\n"
                                             uu____6415 uu____6416);
                                      (let uu____6417 =
                                         let uu____6420 =
                                           let uu____6421 =
                                             FStar_TypeChecker_TcTerm.universe_of
                                               env typ
                                              in
                                           FStar_Syntax_Util.mk_eq2
                                             uu____6421 typ t2 ut
                                            in
                                         add_irrelevant_goal
                                           "rewrite_rec equation" env
                                           uu____6420 opts
                                          in
                                       bind uu____6417
                                         (fun uu____6428  ->
                                            let uu____6429 =
                                              bind rewriter
                                                (fun uu____6443  ->
                                                   let ut1 =
                                                     FStar_TypeChecker_Normalize.reduce_uvar_solutions
                                                       env ut
                                                      in
                                                   log ps
                                                     (fun uu____6449  ->
                                                        let uu____6450 =
                                                          FStar_Syntax_Print.term_to_string
                                                            t2
                                                           in
                                                        let uu____6451 =
                                                          FStar_Syntax_Print.term_to_string
                                                            ut1
                                                           in
                                                        FStar_Util.print2
                                                          "rewrite_rec: succeeded rewriting\n\t%s to\n\t%s\n"
                                                          uu____6450
                                                          uu____6451);
                                                   ret (ut1, ctrl1))
                                               in
                                            focus uu____6429))))))
  
let (topdown_rewrite :
  (FStar_Syntax_Syntax.term ->
     (Prims.bool,FStar_BigInt.t) FStar_Pervasives_Native.tuple2 tac)
    -> Prims.unit tac -> Prims.unit tac)
  =
  fun ctrl  ->
    fun rewriter  ->
      bind get
        (fun ps  ->
           let uu____6495 =
             match ps.FStar_Tactics_Types.goals with
             | g::gs -> (g, gs)
             | [] -> failwith "Pointwise: no goals"  in
           match uu____6495 with
           | (g,gs) ->
               let gt1 = g.FStar_Tactics_Types.goal_ty  in
               (log ps
                  (fun uu____6532  ->
                     let uu____6533 = FStar_Syntax_Print.term_to_string gt1
                        in
                     FStar_Util.print1 "Pointwise starting with %s\n"
                       uu____6533);
                bind dismiss_all
                  (fun uu____6536  ->
                     let uu____6537 =
                       ctrl_tac_fold
                         (rewrite_rec ps ctrl rewriter
                            g.FStar_Tactics_Types.opts)
                         g.FStar_Tactics_Types.context keepGoing gt1
                        in
                     bind uu____6537
                       (fun uu____6555  ->
                          match uu____6555 with
                          | (gt',uu____6563) ->
                              (log ps
                                 (fun uu____6567  ->
                                    let uu____6568 =
                                      FStar_Syntax_Print.term_to_string gt'
                                       in
                                    FStar_Util.print1
                                      "Pointwise seems to have succeded with %s\n"
                                      uu____6568);
                               (let uu____6569 = push_goals gs  in
                                bind uu____6569
                                  (fun uu____6573  ->
                                     add_goals
                                       [(let uu___108_6575 = g  in
                                         {
                                           FStar_Tactics_Types.context =
                                             (uu___108_6575.FStar_Tactics_Types.context);
                                           FStar_Tactics_Types.witness =
                                             (uu___108_6575.FStar_Tactics_Types.witness);
                                           FStar_Tactics_Types.goal_ty = gt';
                                           FStar_Tactics_Types.opts =
                                             (uu___108_6575.FStar_Tactics_Types.opts);
                                           FStar_Tactics_Types.is_guard =
                                             (uu___108_6575.FStar_Tactics_Types.is_guard)
                                         })])))))))
  
let (pointwise :
  FStar_Tactics_Types.direction -> Prims.unit tac -> Prims.unit tac) =
  fun d  ->
    fun tau  ->
      bind get
        (fun ps  ->
           let uu____6597 =
             match ps.FStar_Tactics_Types.goals with
             | g::gs -> (g, gs)
             | [] -> failwith "Pointwise: no goals"  in
           match uu____6597 with
           | (g,gs) ->
               let gt1 = g.FStar_Tactics_Types.goal_ty  in
               (log ps
                  (fun uu____6634  ->
                     let uu____6635 = FStar_Syntax_Print.term_to_string gt1
                        in
                     FStar_Util.print1 "Pointwise starting with %s\n"
                       uu____6635);
                bind dismiss_all
                  (fun uu____6638  ->
                     let uu____6639 =
                       tac_fold_env d
                         (pointwise_rec ps tau g.FStar_Tactics_Types.opts)
                         g.FStar_Tactics_Types.context gt1
                        in
                     bind uu____6639
                       (fun gt'  ->
                          log ps
                            (fun uu____6649  ->
                               let uu____6650 =
                                 FStar_Syntax_Print.term_to_string gt'  in
                               FStar_Util.print1
                                 "Pointwise seems to have succeded with %s\n"
                                 uu____6650);
                          (let uu____6651 = push_goals gs  in
                           bind uu____6651
                             (fun uu____6655  ->
                                add_goals
                                  [(let uu___109_6657 = g  in
                                    {
                                      FStar_Tactics_Types.context =
                                        (uu___109_6657.FStar_Tactics_Types.context);
                                      FStar_Tactics_Types.witness =
                                        (uu___109_6657.FStar_Tactics_Types.witness);
                                      FStar_Tactics_Types.goal_ty = gt';
                                      FStar_Tactics_Types.opts =
                                        (uu___109_6657.FStar_Tactics_Types.opts);
                                      FStar_Tactics_Types.is_guard =
                                        (uu___109_6657.FStar_Tactics_Types.is_guard)
                                    })]))))))
  
let (trefl : Prims.unit tac) =
  bind cur_goal
    (fun g  ->
       let uu____6677 =
         FStar_Syntax_Util.un_squash g.FStar_Tactics_Types.goal_ty  in
       match uu____6677 with
       | FStar_Pervasives_Native.Some t ->
           let uu____6689 = FStar_Syntax_Util.head_and_args' t  in
           (match uu____6689 with
            | (hd1,args) ->
                let uu____6722 =
                  let uu____6735 =
                    let uu____6736 = FStar_Syntax_Util.un_uinst hd1  in
                    uu____6736.FStar_Syntax_Syntax.n  in
                  (uu____6735, args)  in
                (match uu____6722 with
                 | (FStar_Syntax_Syntax.Tm_fvar
                    fv,uu____6750::(l,uu____6752)::(r,uu____6754)::[]) when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.eq2_lid
                     ->
                     let uu____6801 =
                       do_unify g.FStar_Tactics_Types.context l r  in
                     bind uu____6801
                       (fun b  ->
                          if Prims.op_Negation b
                          then
                            let uu____6810 =
                              tts g.FStar_Tactics_Types.context l  in
                            let uu____6811 =
                              tts g.FStar_Tactics_Types.context r  in
                            fail2 "trefl: not a trivial equality (%s vs %s)"
                              uu____6810 uu____6811
                          else solve g FStar_Syntax_Util.exp_unit)
                 | (hd2,uu____6814) ->
                     let uu____6831 = tts g.FStar_Tactics_Types.context t  in
                     fail1 "trefl: not an equality (%s)" uu____6831))
       | FStar_Pervasives_Native.None  -> fail "not an irrelevant goal")
  
let (dup : Prims.unit tac) =
  bind cur_goal
    (fun g  ->
       let uu____6841 =
         new_uvar "dup" g.FStar_Tactics_Types.context
           g.FStar_Tactics_Types.goal_ty
          in
       bind uu____6841
         (fun u  ->
            let g' =
              let uu___110_6848 = g  in
              {
                FStar_Tactics_Types.context =
                  (uu___110_6848.FStar_Tactics_Types.context);
                FStar_Tactics_Types.witness = u;
                FStar_Tactics_Types.goal_ty =
                  (uu___110_6848.FStar_Tactics_Types.goal_ty);
                FStar_Tactics_Types.opts =
                  (uu___110_6848.FStar_Tactics_Types.opts);
                FStar_Tactics_Types.is_guard =
                  (uu___110_6848.FStar_Tactics_Types.is_guard)
              }  in
            bind dismiss
              (fun uu____6851  ->
                 let uu____6852 =
                   let uu____6855 =
                     let uu____6856 =
                       FStar_TypeChecker_TcTerm.universe_of
                         g.FStar_Tactics_Types.context
                         g.FStar_Tactics_Types.goal_ty
                        in
                     FStar_Syntax_Util.mk_eq2 uu____6856
                       g.FStar_Tactics_Types.goal_ty u
                       g.FStar_Tactics_Types.witness
                      in
                   add_irrelevant_goal "dup equation"
                     g.FStar_Tactics_Types.context uu____6855
                     g.FStar_Tactics_Types.opts
                    in
                 bind uu____6852
                   (fun uu____6859  ->
                      let uu____6860 = add_goals [g']  in
                      bind uu____6860 (fun uu____6864  -> ret ())))))
  
let (flip : Prims.unit tac) =
  bind get
    (fun ps  ->
       match ps.FStar_Tactics_Types.goals with
       | g1::g2::gs ->
           set
             (let uu___111_6883 = ps  in
              {
                FStar_Tactics_Types.main_context =
                  (uu___111_6883.FStar_Tactics_Types.main_context);
                FStar_Tactics_Types.main_goal =
                  (uu___111_6883.FStar_Tactics_Types.main_goal);
                FStar_Tactics_Types.all_implicits =
                  (uu___111_6883.FStar_Tactics_Types.all_implicits);
                FStar_Tactics_Types.goals = (g2 :: g1 :: gs);
                FStar_Tactics_Types.smt_goals =
                  (uu___111_6883.FStar_Tactics_Types.smt_goals);
                FStar_Tactics_Types.depth =
                  (uu___111_6883.FStar_Tactics_Types.depth);
                FStar_Tactics_Types.__dump =
                  (uu___111_6883.FStar_Tactics_Types.__dump);
                FStar_Tactics_Types.psc =
                  (uu___111_6883.FStar_Tactics_Types.psc);
                FStar_Tactics_Types.entry_range =
                  (uu___111_6883.FStar_Tactics_Types.entry_range);
                FStar_Tactics_Types.guard_policy =
                  (uu___111_6883.FStar_Tactics_Types.guard_policy)
              })
       | uu____6884 -> fail "flip: less than 2 goals")
  
let (later : Prims.unit tac) =
  bind get
    (fun ps  ->
       match ps.FStar_Tactics_Types.goals with
       | [] -> ret ()
       | g::gs ->
           set
             (let uu___112_6901 = ps  in
              {
                FStar_Tactics_Types.main_context =
                  (uu___112_6901.FStar_Tactics_Types.main_context);
                FStar_Tactics_Types.main_goal =
                  (uu___112_6901.FStar_Tactics_Types.main_goal);
                FStar_Tactics_Types.all_implicits =
                  (uu___112_6901.FStar_Tactics_Types.all_implicits);
                FStar_Tactics_Types.goals = (FStar_List.append gs [g]);
                FStar_Tactics_Types.smt_goals =
                  (uu___112_6901.FStar_Tactics_Types.smt_goals);
                FStar_Tactics_Types.depth =
                  (uu___112_6901.FStar_Tactics_Types.depth);
                FStar_Tactics_Types.__dump =
                  (uu___112_6901.FStar_Tactics_Types.__dump);
                FStar_Tactics_Types.psc =
                  (uu___112_6901.FStar_Tactics_Types.psc);
                FStar_Tactics_Types.entry_range =
                  (uu___112_6901.FStar_Tactics_Types.entry_range);
                FStar_Tactics_Types.guard_policy =
                  (uu___112_6901.FStar_Tactics_Types.guard_policy)
              }))
  
let (qed : Prims.unit tac) =
  bind get
    (fun ps  ->
       match ps.FStar_Tactics_Types.goals with
       | [] -> ret ()
       | uu____6910 -> fail "Not done!")
  
let (cases :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 tac)
  =
  fun t  ->
    let uu____6928 =
      bind cur_goal
        (fun g  ->
           let uu____6942 = __tc g.FStar_Tactics_Types.context t  in
           bind uu____6942
             (fun uu____6978  ->
                match uu____6978 with
                | (t1,typ,guard) ->
                    let uu____6994 = FStar_Syntax_Util.head_and_args typ  in
                    (match uu____6994 with
                     | (hd1,args) ->
                         let uu____7037 =
                           let uu____7050 =
                             let uu____7051 = FStar_Syntax_Util.un_uinst hd1
                                in
                             uu____7051.FStar_Syntax_Syntax.n  in
                           (uu____7050, args)  in
                         (match uu____7037 with
                          | (FStar_Syntax_Syntax.Tm_fvar
                             fv,(p,uu____7070)::(q,uu____7072)::[]) when
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
                                let uu___113_7110 = g  in
                                let uu____7111 =
                                  FStar_TypeChecker_Env.push_bv
                                    g.FStar_Tactics_Types.context v_p
                                   in
                                {
                                  FStar_Tactics_Types.context = uu____7111;
                                  FStar_Tactics_Types.witness =
                                    (uu___113_7110.FStar_Tactics_Types.witness);
                                  FStar_Tactics_Types.goal_ty =
                                    (uu___113_7110.FStar_Tactics_Types.goal_ty);
                                  FStar_Tactics_Types.opts =
                                    (uu___113_7110.FStar_Tactics_Types.opts);
                                  FStar_Tactics_Types.is_guard =
                                    (uu___113_7110.FStar_Tactics_Types.is_guard)
                                }  in
                              let g2 =
                                let uu___114_7113 = g  in
                                let uu____7114 =
                                  FStar_TypeChecker_Env.push_bv
                                    g.FStar_Tactics_Types.context v_q
                                   in
                                {
                                  FStar_Tactics_Types.context = uu____7114;
                                  FStar_Tactics_Types.witness =
                                    (uu___114_7113.FStar_Tactics_Types.witness);
                                  FStar_Tactics_Types.goal_ty =
                                    (uu___114_7113.FStar_Tactics_Types.goal_ty);
                                  FStar_Tactics_Types.opts =
                                    (uu___114_7113.FStar_Tactics_Types.opts);
                                  FStar_Tactics_Types.is_guard =
                                    (uu___114_7113.FStar_Tactics_Types.is_guard)
                                }  in
                              bind dismiss
                                (fun uu____7121  ->
                                   let uu____7122 = add_goals [g1; g2]  in
                                   bind uu____7122
                                     (fun uu____7131  ->
                                        let uu____7132 =
                                          let uu____7137 =
                                            FStar_Syntax_Syntax.bv_to_name
                                              v_p
                                             in
                                          let uu____7138 =
                                            FStar_Syntax_Syntax.bv_to_name
                                              v_q
                                             in
                                          (uu____7137, uu____7138)  in
                                        ret uu____7132))
                          | uu____7143 ->
                              let uu____7156 =
                                tts g.FStar_Tactics_Types.context typ  in
                              fail1 "Not a disjunction: %s" uu____7156))))
       in
    FStar_All.pipe_left (wrap_err "cases") uu____6928
  
let (set_options : Prims.string -> Prims.unit tac) =
  fun s  ->
    bind cur_goal
      (fun g  ->
         FStar_Options.push ();
         (let uu____7194 = FStar_Util.smap_copy g.FStar_Tactics_Types.opts
             in
          FStar_Options.set uu____7194);
         (let res = FStar_Options.set_options FStar_Options.Set s  in
          let opts' = FStar_Options.peek ()  in
          FStar_Options.pop ();
          (match res with
           | FStar_Getopt.Success  ->
               let g' =
                 let uu___115_7201 = g  in
                 {
                   FStar_Tactics_Types.context =
                     (uu___115_7201.FStar_Tactics_Types.context);
                   FStar_Tactics_Types.witness =
                     (uu___115_7201.FStar_Tactics_Types.witness);
                   FStar_Tactics_Types.goal_ty =
                     (uu___115_7201.FStar_Tactics_Types.goal_ty);
                   FStar_Tactics_Types.opts = opts';
                   FStar_Tactics_Types.is_guard =
                     (uu___115_7201.FStar_Tactics_Types.is_guard)
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
      let uu____7245 =
        bind cur_goal
          (fun goal  ->
             let env =
               FStar_TypeChecker_Env.set_expected_typ
                 goal.FStar_Tactics_Types.context ty
                in
             let uu____7253 = __tc env tm  in
             bind uu____7253
               (fun uu____7273  ->
                  match uu____7273 with
                  | (tm1,typ,guard) ->
                      let uu____7285 =
                        proc_guard "unquote" env guard
                          goal.FStar_Tactics_Types.opts
                         in
                      bind uu____7285 (fun uu____7289  -> ret tm1)))
         in
      FStar_All.pipe_left (wrap_err "unquote") uu____7245
  
let (uvar_env :
  env ->
    FStar_Syntax_Syntax.typ FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.term tac)
  =
  fun env  ->
    fun ty  ->
      let uu____7308 =
        match ty with
        | FStar_Pervasives_Native.Some ty1 -> ret ty1
        | FStar_Pervasives_Native.None  ->
            let uu____7314 =
              let uu____7315 = FStar_Syntax_Util.type_u ()  in
              FStar_All.pipe_left FStar_Pervasives_Native.fst uu____7315  in
            new_uvar "uvar_env.2" env uu____7314
         in
      bind uu____7308
        (fun typ  ->
           let uu____7327 = new_uvar "uvar_env" env typ  in
           bind uu____7327 (fun t  -> ret t))
  
let (unshelve : FStar_Syntax_Syntax.term -> Prims.unit tac) =
  fun t  ->
    let uu____7339 =
      bind cur_goal
        (fun goal  ->
           let uu____7345 = __tc goal.FStar_Tactics_Types.context t  in
           bind uu____7345
             (fun uu____7365  ->
                match uu____7365 with
                | (t1,typ,guard) ->
                    let uu____7377 =
                      proc_guard "unshelve" goal.FStar_Tactics_Types.context
                        guard goal.FStar_Tactics_Types.opts
                       in
                    bind uu____7377
                      (fun uu____7382  ->
                         let uu____7383 =
                           let uu____7386 =
                             let uu___116_7387 = goal  in
                             let uu____7388 =
                               bnorm goal.FStar_Tactics_Types.context t1  in
                             let uu____7389 =
                               bnorm goal.FStar_Tactics_Types.context typ  in
                             {
                               FStar_Tactics_Types.context =
                                 (uu___116_7387.FStar_Tactics_Types.context);
                               FStar_Tactics_Types.witness = uu____7388;
                               FStar_Tactics_Types.goal_ty = uu____7389;
                               FStar_Tactics_Types.opts =
                                 (uu___116_7387.FStar_Tactics_Types.opts);
                               FStar_Tactics_Types.is_guard = false
                             }  in
                           [uu____7386]  in
                         add_goals uu____7383)))
       in
    FStar_All.pipe_left (wrap_err "unshelve") uu____7339
  
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
          (fun uu____7422  ->
             let uu____7423 = FStar_Options.unsafe_tactic_exec ()  in
             if uu____7423
             then
               let s =
                 FStar_Util.launch_process true "tactic_launch" prog args
                   input (fun uu____7429  -> fun uu____7430  -> false)
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
        (fun uu____7444  ->
           let uu____7445 =
             FStar_Syntax_Syntax.gen_bv nm FStar_Pervasives_Native.None t  in
           ret uu____7445)
  
let (change : FStar_Syntax_Syntax.typ -> Prims.unit tac) =
  fun ty  ->
    let uu____7453 =
      mlog
        (fun uu____7458  ->
           let uu____7459 = FStar_Syntax_Print.term_to_string ty  in
           FStar_Util.print1 "change: ty = %s\n" uu____7459)
        (fun uu____7461  ->
           bind cur_goal
             (fun g  ->
                let uu____7465 = __tc g.FStar_Tactics_Types.context ty  in
                bind uu____7465
                  (fun uu____7485  ->
                     match uu____7485 with
                     | (ty1,uu____7495,guard) ->
                         let uu____7497 =
                           proc_guard "change" g.FStar_Tactics_Types.context
                             guard g.FStar_Tactics_Types.opts
                            in
                         bind uu____7497
                           (fun uu____7502  ->
                              let uu____7503 =
                                do_unify g.FStar_Tactics_Types.context
                                  g.FStar_Tactics_Types.goal_ty ty1
                                 in
                              bind uu____7503
                                (fun bb  ->
                                   if bb
                                   then
                                     replace_cur
                                       (let uu___117_7512 = g  in
                                        {
                                          FStar_Tactics_Types.context =
                                            (uu___117_7512.FStar_Tactics_Types.context);
                                          FStar_Tactics_Types.witness =
                                            (uu___117_7512.FStar_Tactics_Types.witness);
                                          FStar_Tactics_Types.goal_ty = ty1;
                                          FStar_Tactics_Types.opts =
                                            (uu___117_7512.FStar_Tactics_Types.opts);
                                          FStar_Tactics_Types.is_guard =
                                            (uu___117_7512.FStar_Tactics_Types.is_guard)
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
                                      let uu____7519 =
                                        do_unify
                                          g.FStar_Tactics_Types.context ng
                                          nty
                                         in
                                      bind uu____7519
                                        (fun b  ->
                                           if b
                                           then
                                             replace_cur
                                               (let uu___118_7528 = g  in
                                                {
                                                  FStar_Tactics_Types.context
                                                    =
                                                    (uu___118_7528.FStar_Tactics_Types.context);
                                                  FStar_Tactics_Types.witness
                                                    =
                                                    (uu___118_7528.FStar_Tactics_Types.witness);
                                                  FStar_Tactics_Types.goal_ty
                                                    = ty1;
                                                  FStar_Tactics_Types.opts =
                                                    (uu___118_7528.FStar_Tactics_Types.opts);
                                                  FStar_Tactics_Types.is_guard
                                                    =
                                                    (uu___118_7528.FStar_Tactics_Types.is_guard)
                                                })
                                           else fail "not convertible")))))))
       in
    FStar_All.pipe_left (wrap_err "change") uu____7453
  
let (goal_of_goal_ty :
  env ->
    FStar_Syntax_Syntax.typ ->
      (FStar_Tactics_Types.goal,FStar_TypeChecker_Env.guard_t)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun typ  ->
      let uu____7548 =
        FStar_TypeChecker_Util.new_implicit_var "proofstate_of_goal_ty"
          typ.FStar_Syntax_Syntax.pos env typ
         in
      match uu____7548 with
      | (u,uu____7566,g_u) ->
          let g =
            let uu____7581 = FStar_Options.peek ()  in
            {
              FStar_Tactics_Types.context = env;
              FStar_Tactics_Types.witness = u;
              FStar_Tactics_Types.goal_ty = typ;
              FStar_Tactics_Types.opts = uu____7581;
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
      let uu____7592 = goal_of_goal_ty env typ  in
      match uu____7592 with
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
  