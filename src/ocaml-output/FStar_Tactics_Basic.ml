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
          then dump_proofstate ps (Prims.strcat "TACTING FAILING: " msg)
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
  env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let debug_on uu____938 =
          let uu____939 =
            FStar_Options.set_options FStar_Options.Set
              "--debug_level Rel --debug_level RelCheck"
             in
          ()  in
        let debug_off uu____943 =
          let uu____944 = FStar_Options.set_options FStar_Options.Reset ""
             in
          ()  in
        (let uu____946 =
           FStar_TypeChecker_Env.debug env (FStar_Options.Other "1346")  in
         if uu____946
         then
           (debug_on ();
            (let uu____948 = FStar_Syntax_Print.term_to_string t1  in
             let uu____949 = FStar_Syntax_Print.term_to_string t2  in
             FStar_Util.print2 "%%%%%%%%do_unify %s =? %s\n" uu____948
               uu____949))
         else ());
        (try
           let res = FStar_TypeChecker_Rel.teq_nosmt env t1 t2  in
           debug_off (); res
         with | uu____961 -> (debug_off (); false))
  
let (trysolve :
  FStar_Tactics_Types.goal -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun goal  ->
    fun solution  ->
      do_unify goal.FStar_Tactics_Types.context solution
        goal.FStar_Tactics_Types.witness
  
let (dismiss : Prims.unit tac) =
  bind get
    (fun p  ->
       let uu____974 =
         let uu___61_975 = p  in
         let uu____976 = FStar_List.tl p.FStar_Tactics_Types.goals  in
         {
           FStar_Tactics_Types.main_context =
             (uu___61_975.FStar_Tactics_Types.main_context);
           FStar_Tactics_Types.main_goal =
             (uu___61_975.FStar_Tactics_Types.main_goal);
           FStar_Tactics_Types.all_implicits =
             (uu___61_975.FStar_Tactics_Types.all_implicits);
           FStar_Tactics_Types.goals = uu____976;
           FStar_Tactics_Types.smt_goals =
             (uu___61_975.FStar_Tactics_Types.smt_goals);
           FStar_Tactics_Types.depth =
             (uu___61_975.FStar_Tactics_Types.depth);
           FStar_Tactics_Types.__dump =
             (uu___61_975.FStar_Tactics_Types.__dump);
           FStar_Tactics_Types.psc = (uu___61_975.FStar_Tactics_Types.psc);
           FStar_Tactics_Types.entry_range =
             (uu___61_975.FStar_Tactics_Types.entry_range)
         }  in
       set uu____974)
  
let (solve :
  FStar_Tactics_Types.goal -> FStar_Syntax_Syntax.term -> Prims.unit tac) =
  fun goal  ->
    fun solution  ->
      let uu____989 = trysolve goal solution  in
      if uu____989
      then dismiss
      else
        (let uu____993 =
           let uu____994 = tts goal.FStar_Tactics_Types.context solution  in
           let uu____995 =
             tts goal.FStar_Tactics_Types.context
               goal.FStar_Tactics_Types.witness
              in
           let uu____996 =
             tts goal.FStar_Tactics_Types.context
               goal.FStar_Tactics_Types.goal_ty
              in
           FStar_Util.format3 "%s does not solve %s : %s" uu____994 uu____995
             uu____996
            in
         fail uu____993)
  
let (dismiss_all : Prims.unit tac) =
  bind get
    (fun p  ->
       set
         (let uu___62_1003 = p  in
          {
            FStar_Tactics_Types.main_context =
              (uu___62_1003.FStar_Tactics_Types.main_context);
            FStar_Tactics_Types.main_goal =
              (uu___62_1003.FStar_Tactics_Types.main_goal);
            FStar_Tactics_Types.all_implicits =
              (uu___62_1003.FStar_Tactics_Types.all_implicits);
            FStar_Tactics_Types.goals = [];
            FStar_Tactics_Types.smt_goals =
              (uu___62_1003.FStar_Tactics_Types.smt_goals);
            FStar_Tactics_Types.depth =
              (uu___62_1003.FStar_Tactics_Types.depth);
            FStar_Tactics_Types.__dump =
              (uu___62_1003.FStar_Tactics_Types.__dump);
            FStar_Tactics_Types.psc = (uu___62_1003.FStar_Tactics_Types.psc);
            FStar_Tactics_Types.entry_range =
              (uu___62_1003.FStar_Tactics_Types.entry_range)
          }))
  
let (nwarn : Prims.int FStar_ST.ref) =
  FStar_Util.mk_ref (Prims.parse_int "0") 
let (check_valid_goal : FStar_Tactics_Types.goal -> Prims.unit) =
  fun g  ->
    let uu____1020 = FStar_Options.defensive ()  in
    if uu____1020
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
        let uu____1032 = FStar_TypeChecker_Env.pop_bv e  in
        match uu____1032 with
        | FStar_Pervasives_Native.None  -> b3
        | FStar_Pervasives_Native.Some (bv,e1) ->
            let b4 =
              b3 &&
                (FStar_TypeChecker_Env.closed e1 bv.FStar_Syntax_Syntax.sort)
               in
            aux b4 e1
         in
      let uu____1050 =
        (let uu____1053 = aux b2 env  in Prims.op_Negation uu____1053) &&
          (let uu____1055 = FStar_ST.op_Bang nwarn  in
           uu____1055 < (Prims.parse_int "5"))
         in
      (if uu____1050
       then
         ((let uu____1076 =
             let uu____1081 =
               let uu____1082 = goal_to_string g  in
               FStar_Util.format1
                 "The following goal is ill-formed. Keeping calm and carrying on...\n<%s>\n\n"
                 uu____1082
                in
             (FStar_Errors.Warning_IllFormedGoal, uu____1081)  in
           FStar_Errors.log_issue
             (g.FStar_Tactics_Types.goal_ty).FStar_Syntax_Syntax.pos
             uu____1076);
          (let uu____1083 =
             let uu____1084 = FStar_ST.op_Bang nwarn  in
             uu____1084 + (Prims.parse_int "1")  in
           FStar_ST.op_Colon_Equals nwarn uu____1083))
       else ())
    else ()
  
let (add_goals : FStar_Tactics_Types.goal Prims.list -> Prims.unit tac) =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___63_1142 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___63_1142.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___63_1142.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___63_1142.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (FStar_List.append gs p.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___63_1142.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___63_1142.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___63_1142.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___63_1142.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___63_1142.FStar_Tactics_Types.entry_range)
            }))
  
let (add_smt_goals : FStar_Tactics_Types.goal Prims.list -> Prims.unit tac) =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___64_1160 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___64_1160.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___64_1160.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___64_1160.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___64_1160.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (FStar_List.append gs p.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___64_1160.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___64_1160.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___64_1160.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___64_1160.FStar_Tactics_Types.entry_range)
            }))
  
let (push_goals : FStar_Tactics_Types.goal Prims.list -> Prims.unit tac) =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___65_1178 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___65_1178.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___65_1178.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___65_1178.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (FStar_List.append p.FStar_Tactics_Types.goals gs);
              FStar_Tactics_Types.smt_goals =
                (uu___65_1178.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___65_1178.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___65_1178.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___65_1178.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___65_1178.FStar_Tactics_Types.entry_range)
            }))
  
let (push_smt_goals : FStar_Tactics_Types.goal Prims.list -> Prims.unit tac)
  =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___66_1196 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___66_1196.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___66_1196.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___66_1196.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___66_1196.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (FStar_List.append p.FStar_Tactics_Types.smt_goals gs);
              FStar_Tactics_Types.depth =
                (uu___66_1196.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___66_1196.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___66_1196.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___66_1196.FStar_Tactics_Types.entry_range)
            }))
  
let (replace_cur : FStar_Tactics_Types.goal -> Prims.unit tac) =
  fun g  -> bind dismiss (fun uu____1205  -> add_goals [g]) 
let (add_implicits : implicits -> Prims.unit tac) =
  fun i  ->
    bind get
      (fun p  ->
         set
           (let uu___67_1217 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___67_1217.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___67_1217.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (FStar_List.append i p.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___67_1217.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___67_1217.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___67_1217.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___67_1217.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___67_1217.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___67_1217.FStar_Tactics_Types.entry_range)
            }))
  
let (new_uvar :
  Prims.string ->
    env -> FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.term tac)
  =
  fun reason  ->
    fun env  ->
      fun typ  ->
        let uu____1243 =
          FStar_TypeChecker_Util.new_implicit_var reason
            typ.FStar_Syntax_Syntax.pos env typ
           in
        match uu____1243 with
        | (u,uu____1259,g_u) ->
            let uu____1273 =
              add_implicits g_u.FStar_TypeChecker_Env.implicits  in
            bind uu____1273 (fun uu____1277  -> ret u)
  
let (is_true : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____1281 = FStar_Syntax_Util.un_squash t  in
    match uu____1281 with
    | FStar_Pervasives_Native.Some t' ->
        let uu____1291 =
          let uu____1292 = FStar_Syntax_Subst.compress t'  in
          uu____1292.FStar_Syntax_Syntax.n  in
        (match uu____1291 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.true_lid
         | uu____1296 -> false)
    | uu____1297 -> false
  
let (is_false : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____1305 = FStar_Syntax_Util.un_squash t  in
    match uu____1305 with
    | FStar_Pervasives_Native.Some t' ->
        let uu____1315 =
          let uu____1316 = FStar_Syntax_Subst.compress t'  in
          uu____1316.FStar_Syntax_Syntax.n  in
        (match uu____1315 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.false_lid
         | uu____1320 -> false)
    | uu____1321 -> false
  
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
            let uu____1361 = env.FStar_TypeChecker_Env.universe_of env phi
               in
            FStar_Syntax_Util.mk_squash uu____1361 phi  in
          let uu____1362 = new_uvar reason env typ  in
          bind uu____1362
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
             let uu____1418 =
               (ps.FStar_Tactics_Types.main_context).FStar_TypeChecker_Env.type_of
                 e t
                in
             ret uu____1418
           with
           | ex ->
               let uu____1445 = tts e t  in
               let uu____1446 =
                 let uu____1447 = FStar_TypeChecker_Env.all_binders e  in
                 FStar_All.pipe_right uu____1447
                   (FStar_Syntax_Print.binders_to_string ", ")
                  in
               fail2 "Cannot type %s in context (%s)" uu____1445 uu____1446)
  
let (must_trivial : env -> FStar_TypeChecker_Env.guard_t -> Prims.unit tac) =
  fun e  ->
    fun g  ->
      try
        let uu____1471 =
          let uu____1472 =
            let uu____1473 = FStar_TypeChecker_Rel.discharge_guard_no_smt e g
               in
            FStar_All.pipe_left FStar_TypeChecker_Rel.is_trivial uu____1473
             in
          Prims.op_Negation uu____1472  in
        if uu____1471 then fail "got non-trivial guard" else ret ()
      with | uu____1482 -> fail "got non-trivial guard"
  
let (tc : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.typ tac) =
  fun t  ->
    let uu____1490 =
      bind cur_goal
        (fun goal  ->
           let uu____1496 = __tc goal.FStar_Tactics_Types.context t  in
           bind uu____1496
             (fun uu____1516  ->
                match uu____1516 with
                | (t1,typ,guard) ->
                    let uu____1528 =
                      must_trivial goal.FStar_Tactics_Types.context guard  in
                    bind uu____1528 (fun uu____1532  -> ret typ)))
       in
    FStar_All.pipe_left (wrap_err "tc") uu____1490
  
let (add_irrelevant_goal :
  Prims.string ->
    env ->
      FStar_Syntax_Syntax.typ -> FStar_Options.optionstate -> Prims.unit tac)
  =
  fun reason  ->
    fun env  ->
      fun phi  ->
        fun opts  ->
          let uu____1553 = mk_irrelevant_goal reason env phi opts  in
          bind uu____1553 (fun goal  -> add_goals [goal])
  
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
  
let (trivial : Prims.unit tac) =
  bind cur_goal
    (fun goal  ->
       let uu____1575 =
         istrivial goal.FStar_Tactics_Types.context
           goal.FStar_Tactics_Types.goal_ty
          in
       if uu____1575
       then solve goal FStar_Syntax_Util.exp_unit
       else
         (let uu____1579 =
            tts goal.FStar_Tactics_Types.context
              goal.FStar_Tactics_Types.goal_ty
             in
          fail1 "Not a trivial goal: %s" uu____1579))
  
let (add_goal_from_guard :
  Prims.string ->
    env ->
      FStar_TypeChecker_Env.guard_t ->
        FStar_Options.optionstate -> Prims.unit tac)
  =
  fun reason  ->
    fun e  ->
      fun g  ->
        fun opts  ->
          let uu____1596 =
            let uu____1597 = FStar_TypeChecker_Rel.simplify_guard e g  in
            uu____1597.FStar_TypeChecker_Env.guard_f  in
          match uu____1596 with
          | FStar_TypeChecker_Common.Trivial  -> ret ()
          | FStar_TypeChecker_Common.NonTrivial f ->
              let uu____1601 = istrivial e f  in
              if uu____1601
              then ret ()
              else
                (let uu____1605 = mk_irrelevant_goal reason e f opts  in
                 bind uu____1605
                   (fun goal  ->
                      let goal1 =
                        let uu___72_1612 = goal  in
                        {
                          FStar_Tactics_Types.context =
                            (uu___72_1612.FStar_Tactics_Types.context);
                          FStar_Tactics_Types.witness =
                            (uu___72_1612.FStar_Tactics_Types.witness);
                          FStar_Tactics_Types.goal_ty =
                            (uu___72_1612.FStar_Tactics_Types.goal_ty);
                          FStar_Tactics_Types.opts =
                            (uu___72_1612.FStar_Tactics_Types.opts);
                          FStar_Tactics_Types.is_guard = true
                        }  in
                      push_goals [goal1]))
  
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
          let uu____1633 =
            let uu____1634 = FStar_TypeChecker_Rel.simplify_guard e g  in
            uu____1634.FStar_TypeChecker_Env.guard_f  in
          match uu____1633 with
          | FStar_TypeChecker_Common.Trivial  ->
              ret FStar_Pervasives_Native.None
          | FStar_TypeChecker_Common.NonTrivial f ->
              let uu____1642 = istrivial e f  in
              if uu____1642
              then ret FStar_Pervasives_Native.None
              else
                (let uu____1650 = mk_irrelevant_goal reason e f opts  in
                 bind uu____1650
                   (fun goal  ->
                      ret
                        (FStar_Pervasives_Native.Some
                           (let uu___73_1660 = goal  in
                            {
                              FStar_Tactics_Types.context =
                                (uu___73_1660.FStar_Tactics_Types.context);
                              FStar_Tactics_Types.witness =
                                (uu___73_1660.FStar_Tactics_Types.witness);
                              FStar_Tactics_Types.goal_ty =
                                (uu___73_1660.FStar_Tactics_Types.goal_ty);
                              FStar_Tactics_Types.opts =
                                (uu___73_1660.FStar_Tactics_Types.opts);
                              FStar_Tactics_Types.is_guard = true
                            }))))
  
let (smt : Prims.unit tac) =
  bind cur_goal
    (fun g  ->
       let uu____1668 = is_irrelevant g  in
       if uu____1668
       then bind dismiss (fun uu____1672  -> add_smt_goals [g])
       else
         (let uu____1674 =
            tts g.FStar_Tactics_Types.context g.FStar_Tactics_Types.goal_ty
             in
          fail1 "goal is not irrelevant: cannot dispatch to smt (%s)"
            uu____1674))
  
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
             let uu____1715 =
               try
                 let uu____1749 =
                   let uu____1758 = FStar_BigInt.to_int_fs n1  in
                   FStar_List.splitAt uu____1758 p.FStar_Tactics_Types.goals
                    in
                 ret uu____1749
               with | uu____1780 -> fail "divide: not enough goals"  in
             bind uu____1715
               (fun uu____1807  ->
                  match uu____1807 with
                  | (lgs,rgs) ->
                      let lp =
                        let uu___74_1833 = p  in
                        {
                          FStar_Tactics_Types.main_context =
                            (uu___74_1833.FStar_Tactics_Types.main_context);
                          FStar_Tactics_Types.main_goal =
                            (uu___74_1833.FStar_Tactics_Types.main_goal);
                          FStar_Tactics_Types.all_implicits =
                            (uu___74_1833.FStar_Tactics_Types.all_implicits);
                          FStar_Tactics_Types.goals = lgs;
                          FStar_Tactics_Types.smt_goals = [];
                          FStar_Tactics_Types.depth =
                            (uu___74_1833.FStar_Tactics_Types.depth);
                          FStar_Tactics_Types.__dump =
                            (uu___74_1833.FStar_Tactics_Types.__dump);
                          FStar_Tactics_Types.psc =
                            (uu___74_1833.FStar_Tactics_Types.psc);
                          FStar_Tactics_Types.entry_range =
                            (uu___74_1833.FStar_Tactics_Types.entry_range)
                        }  in
                      let rp =
                        let uu___75_1835 = p  in
                        {
                          FStar_Tactics_Types.main_context =
                            (uu___75_1835.FStar_Tactics_Types.main_context);
                          FStar_Tactics_Types.main_goal =
                            (uu___75_1835.FStar_Tactics_Types.main_goal);
                          FStar_Tactics_Types.all_implicits =
                            (uu___75_1835.FStar_Tactics_Types.all_implicits);
                          FStar_Tactics_Types.goals = rgs;
                          FStar_Tactics_Types.smt_goals = [];
                          FStar_Tactics_Types.depth =
                            (uu___75_1835.FStar_Tactics_Types.depth);
                          FStar_Tactics_Types.__dump =
                            (uu___75_1835.FStar_Tactics_Types.__dump);
                          FStar_Tactics_Types.psc =
                            (uu___75_1835.FStar_Tactics_Types.psc);
                          FStar_Tactics_Types.entry_range =
                            (uu___75_1835.FStar_Tactics_Types.entry_range)
                        }  in
                      let uu____1836 = set lp  in
                      bind uu____1836
                        (fun uu____1844  ->
                           bind l
                             (fun a  ->
                                bind get
                                  (fun lp'  ->
                                     let uu____1858 = set rp  in
                                     bind uu____1858
                                       (fun uu____1866  ->
                                          bind r
                                            (fun b  ->
                                               bind get
                                                 (fun rp'  ->
                                                    let p' =
                                                      let uu___76_1882 = p
                                                         in
                                                      {
                                                        FStar_Tactics_Types.main_context
                                                          =
                                                          (uu___76_1882.FStar_Tactics_Types.main_context);
                                                        FStar_Tactics_Types.main_goal
                                                          =
                                                          (uu___76_1882.FStar_Tactics_Types.main_goal);
                                                        FStar_Tactics_Types.all_implicits
                                                          =
                                                          (uu___76_1882.FStar_Tactics_Types.all_implicits);
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
                                                          (uu___76_1882.FStar_Tactics_Types.depth);
                                                        FStar_Tactics_Types.__dump
                                                          =
                                                          (uu___76_1882.FStar_Tactics_Types.__dump);
                                                        FStar_Tactics_Types.psc
                                                          =
                                                          (uu___76_1882.FStar_Tactics_Types.psc);
                                                        FStar_Tactics_Types.entry_range
                                                          =
                                                          (uu___76_1882.FStar_Tactics_Types.entry_range)
                                                      }  in
                                                    let uu____1883 = set p'
                                                       in
                                                    bind uu____1883
                                                      (fun uu____1891  ->
                                                         ret (a, b))))))))))
  
let focus : 'a . 'a tac -> 'a tac =
  fun f  ->
    let uu____1909 = divide FStar_BigInt.one f idtac  in
    bind uu____1909
      (fun uu____1922  -> match uu____1922 with | (a,()) -> ret a)
  
let rec map : 'a . 'a tac -> 'a Prims.list tac =
  fun tau  ->
    bind get
      (fun p  ->
         match p.FStar_Tactics_Types.goals with
         | [] -> ret []
         | uu____1956::uu____1957 ->
             let uu____1960 =
               let uu____1969 = map tau  in
               divide FStar_BigInt.one tau uu____1969  in
             bind uu____1960
               (fun uu____1987  ->
                  match uu____1987 with | (h,t) -> ret (h :: t)))
  
let (seq : Prims.unit tac -> Prims.unit tac -> Prims.unit tac) =
  fun t1  ->
    fun t2  ->
      let uu____2024 =
        bind t1
          (fun uu____2029  ->
             let uu____2030 = map t2  in
             bind uu____2030 (fun uu____2038  -> ret ()))
         in
      focus uu____2024
  
let (intro : FStar_Syntax_Syntax.binder tac) =
  let uu____2045 =
    bind cur_goal
      (fun goal  ->
         let uu____2054 =
           FStar_Syntax_Util.arrow_one goal.FStar_Tactics_Types.goal_ty  in
         match uu____2054 with
         | FStar_Pervasives_Native.Some (b,c) ->
             let uu____2069 =
               let uu____2070 = FStar_Syntax_Util.is_total_comp c  in
               Prims.op_Negation uu____2070  in
             if uu____2069
             then fail "Codomain is effectful"
             else
               (let env' =
                  FStar_TypeChecker_Env.push_binders
                    goal.FStar_Tactics_Types.context [b]
                   in
                let typ' = comp_to_typ c  in
                let uu____2076 = new_uvar "intro" env' typ'  in
                bind uu____2076
                  (fun u  ->
                     let uu____2083 =
                       let uu____2084 =
                         FStar_Syntax_Util.abs [b] u
                           FStar_Pervasives_Native.None
                          in
                       trysolve goal uu____2084  in
                     if uu____2083
                     then
                       let uu____2087 =
                         let uu____2090 =
                           let uu___79_2091 = goal  in
                           let uu____2092 = bnorm env' u  in
                           let uu____2093 = bnorm env' typ'  in
                           {
                             FStar_Tactics_Types.context = env';
                             FStar_Tactics_Types.witness = uu____2092;
                             FStar_Tactics_Types.goal_ty = uu____2093;
                             FStar_Tactics_Types.opts =
                               (uu___79_2091.FStar_Tactics_Types.opts);
                             FStar_Tactics_Types.is_guard =
                               (uu___79_2091.FStar_Tactics_Types.is_guard)
                           }  in
                         replace_cur uu____2090  in
                       bind uu____2087 (fun uu____2095  -> ret b)
                     else fail "unification failed"))
         | FStar_Pervasives_Native.None  ->
             let uu____2101 =
               tts goal.FStar_Tactics_Types.context
                 goal.FStar_Tactics_Types.goal_ty
                in
             fail1 "goal is not an arrow (%s)" uu____2101)
     in
  FStar_All.pipe_left (wrap_err "intro") uu____2045 
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
       (let uu____2132 =
          FStar_Syntax_Util.arrow_one goal.FStar_Tactics_Types.goal_ty  in
        match uu____2132 with
        | FStar_Pervasives_Native.Some (b,c) ->
            let uu____2151 =
              let uu____2152 = FStar_Syntax_Util.is_total_comp c  in
              Prims.op_Negation uu____2152  in
            if uu____2151
            then fail "Codomain is effectful"
            else
              (let bv =
                 FStar_Syntax_Syntax.gen_bv "__recf"
                   FStar_Pervasives_Native.None
                   goal.FStar_Tactics_Types.goal_ty
                  in
               let bs =
                 let uu____2168 = FStar_Syntax_Syntax.mk_binder bv  in
                 [uu____2168; b]  in
               let env' =
                 FStar_TypeChecker_Env.push_binders
                   goal.FStar_Tactics_Types.context bs
                  in
               let uu____2170 =
                 let uu____2173 = comp_to_typ c  in
                 new_uvar "intro_rec" env' uu____2173  in
               bind uu____2170
                 (fun u  ->
                    let lb =
                      let uu____2189 =
                        FStar_Syntax_Util.abs [b] u
                          FStar_Pervasives_Native.None
                         in
                      FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl bv) []
                        goal.FStar_Tactics_Types.goal_ty
                        FStar_Parser_Const.effect_Tot_lid uu____2189 []
                        FStar_Range.dummyRange
                       in
                    let body = FStar_Syntax_Syntax.bv_to_name bv  in
                    let uu____2195 =
                      FStar_Syntax_Subst.close_let_rec [lb] body  in
                    match uu____2195 with
                    | (lbs,body1) ->
                        let tm =
                          FStar_Syntax_Syntax.mk
                            (FStar_Syntax_Syntax.Tm_let ((true, lbs), body1))
                            FStar_Pervasives_Native.None
                            (goal.FStar_Tactics_Types.witness).FStar_Syntax_Syntax.pos
                           in
                        let res = trysolve goal tm  in
                        if res
                        then
                          let uu____2232 =
                            let uu____2235 =
                              let uu___80_2236 = goal  in
                              let uu____2237 = bnorm env' u  in
                              let uu____2238 =
                                let uu____2239 = comp_to_typ c  in
                                bnorm env' uu____2239  in
                              {
                                FStar_Tactics_Types.context = env';
                                FStar_Tactics_Types.witness = uu____2237;
                                FStar_Tactics_Types.goal_ty = uu____2238;
                                FStar_Tactics_Types.opts =
                                  (uu___80_2236.FStar_Tactics_Types.opts);
                                FStar_Tactics_Types.is_guard =
                                  (uu___80_2236.FStar_Tactics_Types.is_guard)
                              }  in
                            replace_cur uu____2235  in
                          bind uu____2232
                            (fun uu____2246  ->
                               let uu____2247 =
                                 let uu____2252 =
                                   FStar_Syntax_Syntax.mk_binder bv  in
                                 (uu____2252, b)  in
                               ret uu____2247)
                        else fail "intro_rec: unification failed"))
        | FStar_Pervasives_Native.None  ->
            let uu____2266 =
              tts goal.FStar_Tactics_Types.context
                goal.FStar_Tactics_Types.goal_ty
               in
            fail1 "intro_rec: goal is not an arrow (%s)" uu____2266))
  
let (norm : FStar_Syntax_Embeddings.norm_step Prims.list -> Prims.unit tac) =
  fun s  ->
    bind cur_goal
      (fun goal  ->
         mlog
           (fun uu____2286  ->
              let uu____2287 =
                FStar_Syntax_Print.term_to_string
                  goal.FStar_Tactics_Types.witness
                 in
              FStar_Util.print1 "norm: witness = %s\n" uu____2287)
           (fun uu____2292  ->
              let steps =
                let uu____2296 = FStar_TypeChecker_Normalize.tr_norm_steps s
                   in
                FStar_List.append
                  [FStar_TypeChecker_Normalize.Reify;
                  FStar_TypeChecker_Normalize.UnfoldTac] uu____2296
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
                (let uu___81_2303 = goal  in
                 {
                   FStar_Tactics_Types.context =
                     (uu___81_2303.FStar_Tactics_Types.context);
                   FStar_Tactics_Types.witness = w;
                   FStar_Tactics_Types.goal_ty = t;
                   FStar_Tactics_Types.opts =
                     (uu___81_2303.FStar_Tactics_Types.opts);
                   FStar_Tactics_Types.is_guard =
                     (uu___81_2303.FStar_Tactics_Types.is_guard)
                 })))
  
let (norm_term_env :
  env ->
    FStar_Syntax_Embeddings.norm_step Prims.list ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac)
  =
  fun e  ->
    fun s  ->
      fun t  ->
        let uu____2321 =
          mlog
            (fun uu____2326  ->
               let uu____2327 = FStar_Syntax_Print.term_to_string t  in
               FStar_Util.print1 "norm_term: tm = %s\n" uu____2327)
            (fun uu____2329  ->
               bind get
                 (fun ps  ->
                    mlog
                      (fun uu____2334  ->
                         let uu____2335 =
                           tts ps.FStar_Tactics_Types.main_context t  in
                         FStar_Util.print1 "norm_term_env: t = %s\n"
                           uu____2335)
                      (fun uu____2338  ->
                         let uu____2339 = __tc e t  in
                         bind uu____2339
                           (fun uu____2361  ->
                              match uu____2361 with
                              | (t1,uu____2371,guard) ->
                                  (FStar_TypeChecker_Rel.force_trivial_guard
                                     e guard;
                                   (let steps =
                                      let uu____2377 =
                                        FStar_TypeChecker_Normalize.tr_norm_steps
                                          s
                                         in
                                      FStar_List.append
                                        [FStar_TypeChecker_Normalize.Reify;
                                        FStar_TypeChecker_Normalize.UnfoldTac]
                                        uu____2377
                                       in
                                    let t2 =
                                      normalize steps
                                        ps.FStar_Tactics_Types.main_context
                                        t1
                                       in
                                    ret t2))))))
           in
        FStar_All.pipe_left (wrap_err "norm_term") uu____2321
  
let (refine_intro : Prims.unit tac) =
  let uu____2389 =
    bind cur_goal
      (fun g  ->
         let uu____2396 =
           FStar_TypeChecker_Rel.base_and_refinement
             g.FStar_Tactics_Types.context g.FStar_Tactics_Types.goal_ty
            in
         match uu____2396 with
         | (uu____2409,FStar_Pervasives_Native.None ) ->
             fail "not a refinement"
         | (t,FStar_Pervasives_Native.Some (bv,phi)) ->
             let g1 =
               let uu___82_2434 = g  in
               {
                 FStar_Tactics_Types.context =
                   (uu___82_2434.FStar_Tactics_Types.context);
                 FStar_Tactics_Types.witness =
                   (uu___82_2434.FStar_Tactics_Types.witness);
                 FStar_Tactics_Types.goal_ty = t;
                 FStar_Tactics_Types.opts =
                   (uu___82_2434.FStar_Tactics_Types.opts);
                 FStar_Tactics_Types.is_guard =
                   (uu___82_2434.FStar_Tactics_Types.is_guard)
               }  in
             let uu____2435 =
               let uu____2440 =
                 let uu____2445 =
                   let uu____2446 = FStar_Syntax_Syntax.mk_binder bv  in
                   [uu____2446]  in
                 FStar_Syntax_Subst.open_term uu____2445 phi  in
               match uu____2440 with
               | (bvs,phi1) ->
                   let uu____2453 =
                     let uu____2454 = FStar_List.hd bvs  in
                     FStar_Pervasives_Native.fst uu____2454  in
                   (uu____2453, phi1)
                in
             (match uu____2435 with
              | (bv1,phi1) ->
                  let uu____2467 =
                    let uu____2470 =
                      FStar_Syntax_Subst.subst
                        [FStar_Syntax_Syntax.NT
                           (bv1, (g.FStar_Tactics_Types.witness))] phi1
                       in
                    mk_irrelevant_goal "refine_intro refinement"
                      g.FStar_Tactics_Types.context uu____2470
                      g.FStar_Tactics_Types.opts
                     in
                  bind uu____2467
                    (fun g2  ->
                       bind dismiss (fun uu____2474  -> add_goals [g1; g2]))))
     in
  FStar_All.pipe_left (wrap_err "refine_intro") uu____2389 
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
             let uu____2498 = __tc env t  in
             bind uu____2498
               (fun uu____2518  ->
                  match uu____2518 with
                  | (t1,typ,guard) ->
                      let uu____2530 =
                        if force_guard
                        then
                          must_trivial goal.FStar_Tactics_Types.context guard
                        else
                          add_goal_from_guard "__exact typing"
                            goal.FStar_Tactics_Types.context guard
                            goal.FStar_Tactics_Types.opts
                         in
                      bind uu____2530
                        (fun uu____2537  ->
                           mlog
                             (fun uu____2541  ->
                                let uu____2542 =
                                  tts goal.FStar_Tactics_Types.context typ
                                   in
                                let uu____2543 =
                                  tts goal.FStar_Tactics_Types.context
                                    goal.FStar_Tactics_Types.goal_ty
                                   in
                                FStar_Util.print2
                                  "exact: unifying %s and %s\n" uu____2542
                                  uu____2543)
                             (fun uu____2546  ->
                                let uu____2547 =
                                  do_unify goal.FStar_Tactics_Types.context
                                    typ goal.FStar_Tactics_Types.goal_ty
                                   in
                                if uu____2547
                                then solve goal t1
                                else
                                  (let uu____2551 =
                                     tts goal.FStar_Tactics_Types.context t1
                                      in
                                   let uu____2552 =
                                     tts goal.FStar_Tactics_Types.context typ
                                      in
                                   let uu____2553 =
                                     tts goal.FStar_Tactics_Types.context
                                       goal.FStar_Tactics_Types.goal_ty
                                      in
                                   let uu____2554 =
                                     tts goal.FStar_Tactics_Types.context
                                       goal.FStar_Tactics_Types.witness
                                      in
                                   fail4
                                     "%s : %s does not exactly solve the goal %s (witness = %s)"
                                     uu____2551 uu____2552 uu____2553
                                     uu____2554)))))
  
let (t_exact :
  Prims.bool -> Prims.bool -> FStar_Syntax_Syntax.term -> Prims.unit tac) =
  fun set_expected_typ1  ->
    fun force_guard  ->
      fun tm  ->
        let uu____2568 =
          mlog
            (fun uu____2573  ->
               let uu____2574 = FStar_Syntax_Print.term_to_string tm  in
               FStar_Util.print1 "t_exact: tm = %s\n" uu____2574)
            (fun uu____2577  ->
               let uu____2578 =
                 let uu____2585 =
                   __exact_now set_expected_typ1 force_guard tm  in
                 trytac' uu____2585  in
               bind uu____2578
                 (fun uu___56_2594  ->
                    match uu___56_2594 with
                    | FStar_Util.Inr r -> ret ()
                    | FStar_Util.Inl e ->
                        let uu____2603 =
                          let uu____2610 =
                            let uu____2613 =
                              norm [FStar_Syntax_Embeddings.Delta]  in
                            bind uu____2613
                              (fun uu____2617  ->
                                 bind refine_intro
                                   (fun uu____2619  ->
                                      __exact_now set_expected_typ1
                                        force_guard tm))
                             in
                          trytac' uu____2610  in
                        bind uu____2603
                          (fun uu___55_2626  ->
                             match uu___55_2626 with
                             | FStar_Util.Inr r -> ret ()
                             | FStar_Util.Inl uu____2634 -> fail e)))
           in
        FStar_All.pipe_left (wrap_err "exact") uu____2568
  
let (uvar_free_in_goal :
  FStar_Syntax_Syntax.uvar -> FStar_Tactics_Types.goal -> Prims.bool) =
  fun u  ->
    fun g  ->
      if g.FStar_Tactics_Types.is_guard
      then false
      else
        (let free_uvars =
           let uu____2649 =
             let uu____2656 =
               FStar_Syntax_Free.uvars g.FStar_Tactics_Types.goal_ty  in
             FStar_Util.set_elements uu____2656  in
           FStar_List.map FStar_Pervasives_Native.fst uu____2649  in
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
          let uu____2716 = f x  in
          bind uu____2716
            (fun y  ->
               let uu____2724 = mapM f xs  in
               bind uu____2724 (fun ys  -> ret (y :: ys)))
  
exception NoUnif 
let (uu___is_NoUnif : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with | NoUnif  -> true | uu____2742 -> false
  
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
               (fun uu____2760  ->
                  let uu____2761 = FStar_Syntax_Print.term_to_string tm  in
                  FStar_Util.print1 ">>> Calling __exact(%s)\n" uu____2761)
               (fun uu____2764  ->
                  let uu____2765 =
                    let uu____2770 = t_exact false true tm  in
                    trytac uu____2770  in
                  bind uu____2765
                    (fun uu___57_2777  ->
                       match uu___57_2777 with
                       | FStar_Pervasives_Native.Some r -> ret ()
                       | FStar_Pervasives_Native.None  ->
                           mlog
                             (fun uu____2785  ->
                                let uu____2786 =
                                  FStar_Syntax_Print.term_to_string typ  in
                                FStar_Util.print1 ">>> typ = %s\n" uu____2786)
                             (fun uu____2789  ->
                                let uu____2790 =
                                  FStar_Syntax_Util.arrow_one typ  in
                                match uu____2790 with
                                | FStar_Pervasives_Native.None  ->
                                    FStar_Exn.raise NoUnif
                                | FStar_Pervasives_Native.Some ((bv,aq),c) ->
                                    mlog
                                      (fun uu____2822  ->
                                         let uu____2823 =
                                           FStar_Syntax_Print.binder_to_string
                                             (bv, aq)
                                            in
                                         FStar_Util.print1
                                           "__apply: pushing binder %s\n"
                                           uu____2823)
                                      (fun uu____2826  ->
                                         let uu____2827 =
                                           let uu____2828 =
                                             FStar_Syntax_Util.is_total_comp
                                               c
                                              in
                                           Prims.op_Negation uu____2828  in
                                         if uu____2827
                                         then
                                           fail "apply: not total codomain"
                                         else
                                           (let uu____2832 =
                                              new_uvar "apply"
                                                goal.FStar_Tactics_Types.context
                                                bv.FStar_Syntax_Syntax.sort
                                               in
                                            bind uu____2832
                                              (fun u  ->
                                                 let tm' =
                                                   FStar_Syntax_Syntax.mk_Tm_app
                                                     tm [(u, aq)]
                                                     FStar_Pervasives_Native.None
                                                     tm.FStar_Syntax_Syntax.pos
                                                    in
                                                 let typ' =
                                                   let uu____2852 =
                                                     comp_to_typ c  in
                                                   FStar_All.pipe_left
                                                     (FStar_Syntax_Subst.subst
                                                        [FStar_Syntax_Syntax.NT
                                                           (bv, u)])
                                                     uu____2852
                                                    in
                                                 let uu____2853 =
                                                   __apply uopt tm' typ'  in
                                                 bind uu____2853
                                                   (fun uu____2861  ->
                                                      let u1 =
                                                        bnorm
                                                          goal.FStar_Tactics_Types.context
                                                          u
                                                         in
                                                      let uu____2863 =
                                                        let uu____2864 =
                                                          let uu____2867 =
                                                            let uu____2868 =
                                                              FStar_Syntax_Util.head_and_args
                                                                u1
                                                               in
                                                            FStar_Pervasives_Native.fst
                                                              uu____2868
                                                             in
                                                          FStar_Syntax_Subst.compress
                                                            uu____2867
                                                           in
                                                        uu____2864.FStar_Syntax_Syntax.n
                                                         in
                                                      match uu____2863 with
                                                      | FStar_Syntax_Syntax.Tm_uvar
                                                          (uvar,uu____2896)
                                                          ->
                                                          bind get
                                                            (fun ps  ->
                                                               let uu____2924
                                                                 =
                                                                 uopt &&
                                                                   (uvar_free
                                                                    uvar ps)
                                                                  in
                                                               if uu____2924
                                                               then ret ()
                                                               else
                                                                 (let uu____2928
                                                                    =
                                                                    let uu____2931
                                                                    =
                                                                    let uu___83_2932
                                                                    = goal
                                                                     in
                                                                    let uu____2933
                                                                    =
                                                                    bnorm
                                                                    goal.FStar_Tactics_Types.context
                                                                    u1  in
                                                                    let uu____2934
                                                                    =
                                                                    bnorm
                                                                    goal.FStar_Tactics_Types.context
                                                                    bv.FStar_Syntax_Syntax.sort
                                                                     in
                                                                    {
                                                                    FStar_Tactics_Types.context
                                                                    =
                                                                    (uu___83_2932.FStar_Tactics_Types.context);
                                                                    FStar_Tactics_Types.witness
                                                                    =
                                                                    uu____2933;
                                                                    FStar_Tactics_Types.goal_ty
                                                                    =
                                                                    uu____2934;
                                                                    FStar_Tactics_Types.opts
                                                                    =
                                                                    (uu___83_2932.FStar_Tactics_Types.opts);
                                                                    FStar_Tactics_Types.is_guard
                                                                    = false
                                                                    }  in
                                                                    [uu____2931]
                                                                     in
                                                                  add_goals
                                                                    uu____2928))
                                                      | t -> ret ()))))))))
  
let try_unif : 'a . 'a tac -> 'a tac -> 'a tac =
  fun t  ->
    fun t'  -> mk_tac (fun ps  -> try run t ps with | NoUnif  -> run t' ps)
  
let (apply : Prims.bool -> FStar_Syntax_Syntax.term -> Prims.unit tac) =
  fun uopt  ->
    fun tm  ->
      let uu____2980 =
        mlog
          (fun uu____2985  ->
             let uu____2986 = FStar_Syntax_Print.term_to_string tm  in
             FStar_Util.print1 "apply: tm = %s\n" uu____2986)
          (fun uu____2988  ->
             bind cur_goal
               (fun goal  ->
                  let uu____2992 = __tc goal.FStar_Tactics_Types.context tm
                     in
                  bind uu____2992
                    (fun uu____3013  ->
                       match uu____3013 with
                       | (tm1,typ,guard) ->
                           let uu____3025 =
                             let uu____3028 =
                               let uu____3031 = __apply uopt tm1 typ  in
                               bind uu____3031
                                 (fun uu____3035  ->
                                    add_goal_from_guard "apply guard"
                                      goal.FStar_Tactics_Types.context guard
                                      goal.FStar_Tactics_Types.opts)
                                in
                             focus uu____3028  in
                           let uu____3036 =
                             let uu____3039 =
                               tts goal.FStar_Tactics_Types.context tm1  in
                             let uu____3040 =
                               tts goal.FStar_Tactics_Types.context typ  in
                             let uu____3041 =
                               tts goal.FStar_Tactics_Types.context
                                 goal.FStar_Tactics_Types.goal_ty
                                in
                             fail3
                               "Cannot instantiate %s (of type %s) to match goal (%s)"
                               uu____3039 uu____3040 uu____3041
                              in
                           try_unif uu____3025 uu____3036)))
         in
      FStar_All.pipe_left (wrap_err "apply") uu____2980
  
let (apply_lemma : FStar_Syntax_Syntax.term -> Prims.unit tac) =
  fun tm  ->
    let uu____3053 =
      let uu____3056 =
        mlog
          (fun uu____3061  ->
             let uu____3062 = FStar_Syntax_Print.term_to_string tm  in
             FStar_Util.print1 "apply_lemma: tm = %s\n" uu____3062)
          (fun uu____3065  ->
             let is_unit_t t =
               let uu____3070 =
                 let uu____3071 = FStar_Syntax_Subst.compress t  in
                 uu____3071.FStar_Syntax_Syntax.n  in
               match uu____3070 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.unit_lid
                   -> true
               | uu____3075 -> false  in
             bind cur_goal
               (fun goal  ->
                  let uu____3079 = __tc goal.FStar_Tactics_Types.context tm
                     in
                  bind uu____3079
                    (fun uu____3101  ->
                       match uu____3101 with
                       | (tm1,t,guard) ->
                           let uu____3113 =
                             FStar_Syntax_Util.arrow_formals_comp t  in
                           (match uu____3113 with
                            | (bs,comp) ->
                                if
                                  Prims.op_Negation
                                    (FStar_Syntax_Util.is_lemma_comp comp)
                                then fail "not a lemma"
                                else
                                  (let uu____3143 =
                                     FStar_List.fold_left
                                       (fun uu____3189  ->
                                          fun uu____3190  ->
                                            match (uu____3189, uu____3190)
                                            with
                                            | ((uvs,guard1,subst1),(b,aq)) ->
                                                let b_t =
                                                  FStar_Syntax_Subst.subst
                                                    subst1
                                                    b.FStar_Syntax_Syntax.sort
                                                   in
                                                let uu____3293 =
                                                  is_unit_t b_t  in
                                                if uu____3293
                                                then
                                                  (((FStar_Syntax_Util.exp_unit,
                                                      aq) :: uvs), guard1,
                                                    ((FStar_Syntax_Syntax.NT
                                                        (b,
                                                          FStar_Syntax_Util.exp_unit))
                                                    :: subst1))
                                                else
                                                  (let uu____3331 =
                                                     FStar_TypeChecker_Util.new_implicit_var
                                                       "apply_lemma"
                                                       (goal.FStar_Tactics_Types.goal_ty).FStar_Syntax_Syntax.pos
                                                       goal.FStar_Tactics_Types.context
                                                       b_t
                                                      in
                                                   match uu____3331 with
                                                   | (u,uu____3361,g_u) ->
                                                       let uu____3375 =
                                                         FStar_TypeChecker_Rel.conj_guard
                                                           guard1 g_u
                                                          in
                                                       (((u, aq) :: uvs),
                                                         uu____3375,
                                                         ((FStar_Syntax_Syntax.NT
                                                             (b, u)) ::
                                                         subst1))))
                                       ([], guard, []) bs
                                      in
                                   match uu____3143 with
                                   | (uvs,implicits,subst1) ->
                                       let uvs1 = FStar_List.rev uvs  in
                                       let comp1 =
                                         FStar_Syntax_Subst.subst_comp subst1
                                           comp
                                          in
                                       let uu____3445 =
                                         let uu____3454 =
                                           let uu____3463 =
                                             FStar_Syntax_Util.comp_to_comp_typ
                                               comp1
                                              in
                                           uu____3463.FStar_Syntax_Syntax.effect_args
                                            in
                                         match uu____3454 with
                                         | pre::post::uu____3474 ->
                                             ((FStar_Pervasives_Native.fst
                                                 pre),
                                               (FStar_Pervasives_Native.fst
                                                  post))
                                         | uu____3515 ->
                                             failwith
                                               "apply_lemma: impossible: not a lemma"
                                          in
                                       (match uu____3445 with
                                        | (pre,post) ->
                                            let post1 =
                                              let uu____3547 =
                                                let uu____3556 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    FStar_Syntax_Util.exp_unit
                                                   in
                                                [uu____3556]  in
                                              FStar_Syntax_Util.mk_app post
                                                uu____3547
                                               in
                                            let uu____3557 =
                                              let uu____3558 =
                                                let uu____3559 =
                                                  FStar_Syntax_Util.mk_squash
                                                    FStar_Syntax_Syntax.U_zero
                                                    post1
                                                   in
                                                do_unify
                                                  goal.FStar_Tactics_Types.context
                                                  uu____3559
                                                  goal.FStar_Tactics_Types.goal_ty
                                                 in
                                              Prims.op_Negation uu____3558
                                               in
                                            if uu____3557
                                            then
                                              let uu____3562 =
                                                tts
                                                  goal.FStar_Tactics_Types.context
                                                  tm1
                                                 in
                                              let uu____3563 =
                                                let uu____3564 =
                                                  FStar_Syntax_Util.mk_squash
                                                    FStar_Syntax_Syntax.U_zero
                                                    post1
                                                   in
                                                tts
                                                  goal.FStar_Tactics_Types.context
                                                  uu____3564
                                                 in
                                              let uu____3565 =
                                                tts
                                                  goal.FStar_Tactics_Types.context
                                                  goal.FStar_Tactics_Types.goal_ty
                                                 in
                                              fail3
                                                "Cannot instantiate lemma %s (with postcondition: %s) to match goal (%s)"
                                                uu____3562 uu____3563
                                                uu____3565
                                            else
                                              (let uu____3567 =
                                                 add_implicits
                                                   implicits.FStar_TypeChecker_Env.implicits
                                                  in
                                               bind uu____3567
                                                 (fun uu____3572  ->
                                                    let uu____3573 =
                                                      solve goal
                                                        FStar_Syntax_Util.exp_unit
                                                       in
                                                    bind uu____3573
                                                      (fun uu____3581  ->
                                                         let is_free_uvar uv
                                                           t1 =
                                                           let free_uvars =
                                                             let uu____3592 =
                                                               let uu____3599
                                                                 =
                                                                 FStar_Syntax_Free.uvars
                                                                   t1
                                                                  in
                                                               FStar_Util.set_elements
                                                                 uu____3599
                                                                in
                                                             FStar_List.map
                                                               FStar_Pervasives_Native.fst
                                                               uu____3592
                                                              in
                                                           FStar_List.existsML
                                                             (fun u  ->
                                                                FStar_Syntax_Unionfind.equiv
                                                                  u uv)
                                                             free_uvars
                                                            in
                                                         let appears uv goals
                                                           =
                                                           FStar_List.existsML
                                                             (fun g'  ->
                                                                is_free_uvar
                                                                  uv
                                                                  g'.FStar_Tactics_Types.goal_ty)
                                                             goals
                                                            in
                                                         let checkone t1
                                                           goals =
                                                           let uu____3640 =
                                                             FStar_Syntax_Util.head_and_args
                                                               t1
                                                              in
                                                           match uu____3640
                                                           with
                                                           | (hd1,uu____3656)
                                                               ->
                                                               (match 
                                                                  hd1.FStar_Syntax_Syntax.n
                                                                with
                                                                | FStar_Syntax_Syntax.Tm_uvar
                                                                    (uv,uu____3678)
                                                                    ->
                                                                    appears
                                                                    uv goals
                                                                | uu____3703
                                                                    -> false)
                                                            in
                                                         let uu____3704 =
                                                           FStar_All.pipe_right
                                                             implicits.FStar_TypeChecker_Env.implicits
                                                             (mapM
                                                                (fun
                                                                   uu____3776
                                                                    ->
                                                                   match uu____3776
                                                                   with
                                                                   | 
                                                                   (_msg,env,_uvar,term,typ,uu____3804)
                                                                    ->
                                                                    let uu____3805
                                                                    =
                                                                    FStar_Syntax_Util.head_and_args
                                                                    term  in
                                                                    (match uu____3805
                                                                    with
                                                                    | 
                                                                    (hd1,uu____3831)
                                                                    ->
                                                                    let uu____3852
                                                                    =
                                                                    let uu____3853
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    hd1  in
                                                                    uu____3853.FStar_Syntax_Syntax.n
                                                                     in
                                                                    (match uu____3852
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Tm_uvar
                                                                    uu____3866
                                                                    ->
                                                                    let uu____3883
                                                                    =
                                                                    let uu____3892
                                                                    =
                                                                    let uu____3895
                                                                    =
                                                                    let uu___86_3896
                                                                    = goal
                                                                     in
                                                                    let uu____3897
                                                                    =
                                                                    bnorm
                                                                    goal.FStar_Tactics_Types.context
                                                                    term  in
                                                                    let uu____3898
                                                                    =
                                                                    bnorm
                                                                    goal.FStar_Tactics_Types.context
                                                                    typ  in
                                                                    {
                                                                    FStar_Tactics_Types.context
                                                                    =
                                                                    (uu___86_3896.FStar_Tactics_Types.context);
                                                                    FStar_Tactics_Types.witness
                                                                    =
                                                                    uu____3897;
                                                                    FStar_Tactics_Types.goal_ty
                                                                    =
                                                                    uu____3898;
                                                                    FStar_Tactics_Types.opts
                                                                    =
                                                                    (uu___86_3896.FStar_Tactics_Types.opts);
                                                                    FStar_Tactics_Types.is_guard
                                                                    =
                                                                    (uu___86_3896.FStar_Tactics_Types.is_guard)
                                                                    }  in
                                                                    [uu____3895]
                                                                     in
                                                                    (uu____3892,
                                                                    [])  in
                                                                    ret
                                                                    uu____3883
                                                                    | 
                                                                    uu____3911
                                                                    ->
                                                                    let g_typ
                                                                    =
                                                                    let uu____3913
                                                                    =
                                                                    FStar_Options.__temp_fast_implicits
                                                                    ()  in
                                                                    if
                                                                    uu____3913
                                                                    then
                                                                    FStar_TypeChecker_TcTerm.check_type_of_well_typed_term
                                                                    false env
                                                                    term typ
                                                                    else
                                                                    (let term1
                                                                    =
                                                                    bnorm env
                                                                    term  in
                                                                    let uu____3916
                                                                    =
                                                                    let uu____3923
                                                                    =
                                                                    FStar_TypeChecker_Env.set_expected_typ
                                                                    env typ
                                                                     in
                                                                    env.FStar_TypeChecker_Env.type_of
                                                                    uu____3923
                                                                    term1  in
                                                                    match uu____3916
                                                                    with
                                                                    | 
                                                                    (uu____3924,uu____3925,g_typ)
                                                                    -> g_typ)
                                                                     in
                                                                    let uu____3927
                                                                    =
                                                                    goal_from_guard
                                                                    "apply_lemma solved arg"
                                                                    goal.FStar_Tactics_Types.context
                                                                    g_typ
                                                                    goal.FStar_Tactics_Types.opts
                                                                     in
                                                                    bind
                                                                    uu____3927
                                                                    (fun
                                                                    uu___58_3943
                                                                     ->
                                                                    match uu___58_3943
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
                                                         bind uu____3704
                                                           (fun goals_  ->
                                                              let sub_goals =
                                                                let uu____4011
                                                                  =
                                                                  FStar_List.map
                                                                    FStar_Pervasives_Native.fst
                                                                    goals_
                                                                   in
                                                                FStar_List.flatten
                                                                  uu____4011
                                                                 in
                                                              let smt_goals =
                                                                let uu____4033
                                                                  =
                                                                  FStar_List.map
                                                                    FStar_Pervasives_Native.snd
                                                                    goals_
                                                                   in
                                                                FStar_List.flatten
                                                                  uu____4033
                                                                 in
                                                              let rec filter'
                                                                a f xs =
                                                                match xs with
                                                                | [] -> []
                                                                | x::xs1 ->
                                                                    let uu____4088
                                                                    = f x xs1
                                                                     in
                                                                    if
                                                                    uu____4088
                                                                    then
                                                                    let uu____4091
                                                                    =
                                                                    filter'
                                                                    () f xs1
                                                                     in x ::
                                                                    uu____4091
                                                                    else
                                                                    filter'
                                                                    () f xs1
                                                                 in
                                                              let sub_goals1
                                                                =
                                                                Obj.magic
                                                                  (filter' ()
                                                                    (fun a438
                                                                     ->
                                                                    fun a439 
                                                                    ->
                                                                    (Obj.magic
                                                                    (fun g 
                                                                    ->
                                                                    fun goals
                                                                     ->
                                                                    let uu____4105
                                                                    =
                                                                    checkone
                                                                    g.FStar_Tactics_Types.witness
                                                                    goals  in
                                                                    Prims.op_Negation
                                                                    uu____4105))
                                                                    a438 a439)
                                                                    (Obj.magic
                                                                    sub_goals))
                                                                 in
                                                              let uu____4106
                                                                =
                                                                add_goal_from_guard
                                                                  "apply_lemma guard"
                                                                  goal.FStar_Tactics_Types.context
                                                                  guard
                                                                  goal.FStar_Tactics_Types.opts
                                                                 in
                                                              bind uu____4106
                                                                (fun
                                                                   uu____4111
                                                                    ->
                                                                   let uu____4112
                                                                    =
                                                                    let uu____4115
                                                                    =
                                                                    let uu____4116
                                                                    =
                                                                    let uu____4117
                                                                    =
                                                                    FStar_Syntax_Util.mk_squash
                                                                    FStar_Syntax_Syntax.U_zero
                                                                    pre  in
                                                                    istrivial
                                                                    goal.FStar_Tactics_Types.context
                                                                    uu____4117
                                                                     in
                                                                    Prims.op_Negation
                                                                    uu____4116
                                                                     in
                                                                    if
                                                                    uu____4115
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
                                                                    uu____4112
                                                                    (fun
                                                                    uu____4123
                                                                     ->
                                                                    let uu____4124
                                                                    =
                                                                    add_smt_goals
                                                                    smt_goals
                                                                     in
                                                                    bind
                                                                    uu____4124
                                                                    (fun
                                                                    uu____4128
                                                                     ->
                                                                    add_goals
                                                                    sub_goals1)))))))))))))
         in
      focus uu____3056  in
    FStar_All.pipe_left (wrap_err "apply_lemma") uu____3053
  
let (destruct_eq' :
  FStar_Syntax_Syntax.typ ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun typ  ->
    let uu____4148 = FStar_Syntax_Util.destruct_typ_as_formula typ  in
    match uu____4148 with
    | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn
        (l,uu____4158::(e1,uu____4160)::(e2,uu____4162)::[])) when
        FStar_Ident.lid_equals l FStar_Parser_Const.eq2_lid ->
        FStar_Pervasives_Native.Some (e1, e2)
    | uu____4221 -> FStar_Pervasives_Native.None
  
let (destruct_eq :
  FStar_Syntax_Syntax.typ ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun typ  ->
    let uu____4243 = destruct_eq' typ  in
    match uu____4243 with
    | FStar_Pervasives_Native.Some t -> FStar_Pervasives_Native.Some t
    | FStar_Pervasives_Native.None  ->
        let uu____4273 = FStar_Syntax_Util.un_squash typ  in
        (match uu____4273 with
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
        let uu____4329 = FStar_TypeChecker_Env.pop_bv e1  in
        match uu____4329 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (bv',e') ->
            if FStar_Syntax_Syntax.bv_eq bvar bv'
            then FStar_Pervasives_Native.Some (e', [])
            else
              (let uu____4377 = aux e'  in
               FStar_Util.map_opt uu____4377
                 (fun uu____4401  ->
                    match uu____4401 with | (e'',bvs) -> (e'', (bv' :: bvs))))
         in
      let uu____4422 = aux e  in
      FStar_Util.map_opt uu____4422
        (fun uu____4446  ->
           match uu____4446 with | (e',bvs) -> (e', (FStar_List.rev bvs)))
  
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
          let uu____4501 = split_env b1 g.FStar_Tactics_Types.context  in
          FStar_Util.map_opt uu____4501
            (fun uu____4525  ->
               match uu____4525 with
               | (e0,bvs) ->
                   let s1 bv =
                     let uu___87_4542 = bv  in
                     let uu____4543 =
                       FStar_Syntax_Subst.subst s bv.FStar_Syntax_Syntax.sort
                        in
                     {
                       FStar_Syntax_Syntax.ppname =
                         (uu___87_4542.FStar_Syntax_Syntax.ppname);
                       FStar_Syntax_Syntax.index =
                         (uu___87_4542.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort = uu____4543
                     }  in
                   let bvs1 = FStar_List.map s1 bvs  in
                   let c = push_bvs e0 (b2 :: bvs1)  in
                   let w =
                     FStar_Syntax_Subst.subst s g.FStar_Tactics_Types.witness
                      in
                   let t =
                     FStar_Syntax_Subst.subst s g.FStar_Tactics_Types.goal_ty
                      in
                   let uu___88_4552 = g  in
                   {
                     FStar_Tactics_Types.context = c;
                     FStar_Tactics_Types.witness = w;
                     FStar_Tactics_Types.goal_ty = t;
                     FStar_Tactics_Types.opts =
                       (uu___88_4552.FStar_Tactics_Types.opts);
                     FStar_Tactics_Types.is_guard =
                       (uu___88_4552.FStar_Tactics_Types.is_guard)
                   })
  
let (rewrite : FStar_Syntax_Syntax.binder -> Prims.unit tac) =
  fun h  ->
    bind cur_goal
      (fun goal  ->
         let uu____4565 = h  in
         match uu____4565 with
         | (bv,uu____4569) ->
             mlog
               (fun uu____4573  ->
                  let uu____4574 = FStar_Syntax_Print.bv_to_string bv  in
                  let uu____4575 =
                    tts goal.FStar_Tactics_Types.context
                      bv.FStar_Syntax_Syntax.sort
                     in
                  FStar_Util.print2 "+++Rewrite %s : %s\n" uu____4574
                    uu____4575)
               (fun uu____4578  ->
                  let uu____4579 =
                    split_env bv goal.FStar_Tactics_Types.context  in
                  match uu____4579 with
                  | FStar_Pervasives_Native.None  ->
                      fail "rewrite: binder not found in environment"
                  | FStar_Pervasives_Native.Some (e0,bvs) ->
                      let uu____4608 =
                        destruct_eq bv.FStar_Syntax_Syntax.sort  in
                      (match uu____4608 with
                       | FStar_Pervasives_Native.Some (x,e) ->
                           let uu____4623 =
                             let uu____4624 = FStar_Syntax_Subst.compress x
                                in
                             uu____4624.FStar_Syntax_Syntax.n  in
                           (match uu____4623 with
                            | FStar_Syntax_Syntax.Tm_name x1 ->
                                let s = [FStar_Syntax_Syntax.NT (x1, e)]  in
                                let s1 bv1 =
                                  let uu___89_4637 = bv1  in
                                  let uu____4638 =
                                    FStar_Syntax_Subst.subst s
                                      bv1.FStar_Syntax_Syntax.sort
                                     in
                                  {
                                    FStar_Syntax_Syntax.ppname =
                                      (uu___89_4637.FStar_Syntax_Syntax.ppname);
                                    FStar_Syntax_Syntax.index =
                                      (uu___89_4637.FStar_Syntax_Syntax.index);
                                    FStar_Syntax_Syntax.sort = uu____4638
                                  }  in
                                let bvs1 = FStar_List.map s1 bvs  in
                                let uu____4644 =
                                  let uu___90_4645 = goal  in
                                  let uu____4646 = push_bvs e0 (bv :: bvs1)
                                     in
                                  let uu____4647 =
                                    FStar_Syntax_Subst.subst s
                                      goal.FStar_Tactics_Types.witness
                                     in
                                  let uu____4648 =
                                    FStar_Syntax_Subst.subst s
                                      goal.FStar_Tactics_Types.goal_ty
                                     in
                                  {
                                    FStar_Tactics_Types.context = uu____4646;
                                    FStar_Tactics_Types.witness = uu____4647;
                                    FStar_Tactics_Types.goal_ty = uu____4648;
                                    FStar_Tactics_Types.opts =
                                      (uu___90_4645.FStar_Tactics_Types.opts);
                                    FStar_Tactics_Types.is_guard =
                                      (uu___90_4645.FStar_Tactics_Types.is_guard)
                                  }  in
                                replace_cur uu____4644
                            | uu____4649 ->
                                fail
                                  "rewrite: Not an equality hypothesis with a variable on the LHS")
                       | uu____4650 ->
                           fail "rewrite: Not an equality hypothesis")))
  
let (rename_to :
  FStar_Syntax_Syntax.binder -> Prims.string -> Prims.unit tac) =
  fun b  ->
    fun s  ->
      bind cur_goal
        (fun goal  ->
           let uu____4675 = b  in
           match uu____4675 with
           | (bv,uu____4679) ->
               let bv' =
                 FStar_Syntax_Syntax.freshen_bv
                   (let uu___91_4683 = bv  in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (FStar_Ident.mk_ident
                           (s,
                             ((bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange)));
                      FStar_Syntax_Syntax.index =
                        (uu___91_4683.FStar_Syntax_Syntax.index);
                      FStar_Syntax_Syntax.sort =
                        (uu___91_4683.FStar_Syntax_Syntax.sort)
                    })
                  in
               let s1 =
                 let uu____4687 =
                   let uu____4688 =
                     let uu____4695 = FStar_Syntax_Syntax.bv_to_name bv'  in
                     (bv, uu____4695)  in
                   FStar_Syntax_Syntax.NT uu____4688  in
                 [uu____4687]  in
               let uu____4696 = subst_goal bv bv' s1 goal  in
               (match uu____4696 with
                | FStar_Pervasives_Native.None  ->
                    fail "rename_to: binder not found in environment"
                | FStar_Pervasives_Native.Some goal1 -> replace_cur goal1))
  
let (binder_retype : FStar_Syntax_Syntax.binder -> Prims.unit tac) =
  fun b  ->
    bind cur_goal
      (fun goal  ->
         let uu____4715 = b  in
         match uu____4715 with
         | (bv,uu____4719) ->
             let uu____4720 = split_env bv goal.FStar_Tactics_Types.context
                in
             (match uu____4720 with
              | FStar_Pervasives_Native.None  ->
                  fail "binder_retype: binder is not present in environment"
              | FStar_Pervasives_Native.Some (e0,bvs) ->
                  let uu____4749 = FStar_Syntax_Util.type_u ()  in
                  (match uu____4749 with
                   | (ty,u) ->
                       let uu____4758 = new_uvar "binder_retype" e0 ty  in
                       bind uu____4758
                         (fun t'  ->
                            let bv'' =
                              let uu___92_4768 = bv  in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___92_4768.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___92_4768.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = t'
                              }  in
                            let s =
                              let uu____4772 =
                                let uu____4773 =
                                  let uu____4780 =
                                    FStar_Syntax_Syntax.bv_to_name bv''  in
                                  (bv, uu____4780)  in
                                FStar_Syntax_Syntax.NT uu____4773  in
                              [uu____4772]  in
                            let bvs1 =
                              FStar_List.map
                                (fun b1  ->
                                   let uu___93_4788 = b1  in
                                   let uu____4789 =
                                     FStar_Syntax_Subst.subst s
                                       b1.FStar_Syntax_Syntax.sort
                                      in
                                   {
                                     FStar_Syntax_Syntax.ppname =
                                       (uu___93_4788.FStar_Syntax_Syntax.ppname);
                                     FStar_Syntax_Syntax.index =
                                       (uu___93_4788.FStar_Syntax_Syntax.index);
                                     FStar_Syntax_Syntax.sort = uu____4789
                                   }) bvs
                               in
                            let env' = push_bvs e0 (bv'' :: bvs1)  in
                            bind dismiss
                              (fun uu____4795  ->
                                 let uu____4796 =
                                   let uu____4799 =
                                     let uu____4802 =
                                       let uu___94_4803 = goal  in
                                       let uu____4804 =
                                         FStar_Syntax_Subst.subst s
                                           goal.FStar_Tactics_Types.witness
                                          in
                                       let uu____4805 =
                                         FStar_Syntax_Subst.subst s
                                           goal.FStar_Tactics_Types.goal_ty
                                          in
                                       {
                                         FStar_Tactics_Types.context = env';
                                         FStar_Tactics_Types.witness =
                                           uu____4804;
                                         FStar_Tactics_Types.goal_ty =
                                           uu____4805;
                                         FStar_Tactics_Types.opts =
                                           (uu___94_4803.FStar_Tactics_Types.opts);
                                         FStar_Tactics_Types.is_guard =
                                           (uu___94_4803.FStar_Tactics_Types.is_guard)
                                       }  in
                                     [uu____4802]  in
                                   add_goals uu____4799  in
                                 bind uu____4796
                                   (fun uu____4808  ->
                                      let uu____4809 =
                                        FStar_Syntax_Util.mk_eq2
                                          (FStar_Syntax_Syntax.U_succ u) ty
                                          bv.FStar_Syntax_Syntax.sort t'
                                         in
                                      add_irrelevant_goal
                                        "binder_retype equation" e0
                                        uu____4809
                                        goal.FStar_Tactics_Types.opts))))))
  
let (norm_binder_type :
  FStar_Syntax_Embeddings.norm_step Prims.list ->
    FStar_Syntax_Syntax.binder -> Prims.unit tac)
  =
  fun s  ->
    fun b  ->
      bind cur_goal
        (fun goal  ->
           let uu____4830 = b  in
           match uu____4830 with
           | (bv,uu____4834) ->
               let uu____4835 = split_env bv goal.FStar_Tactics_Types.context
                  in
               (match uu____4835 with
                | FStar_Pervasives_Native.None  ->
                    fail
                      "binder_retype: binder is not present in environment"
                | FStar_Pervasives_Native.Some (e0,bvs) ->
                    let steps =
                      let uu____4867 =
                        FStar_TypeChecker_Normalize.tr_norm_steps s  in
                      FStar_List.append
                        [FStar_TypeChecker_Normalize.Reify;
                        FStar_TypeChecker_Normalize.UnfoldTac] uu____4867
                       in
                    let sort' =
                      normalize steps e0 bv.FStar_Syntax_Syntax.sort  in
                    let bv' =
                      let uu___95_4872 = bv  in
                      {
                        FStar_Syntax_Syntax.ppname =
                          (uu___95_4872.FStar_Syntax_Syntax.ppname);
                        FStar_Syntax_Syntax.index =
                          (uu___95_4872.FStar_Syntax_Syntax.index);
                        FStar_Syntax_Syntax.sort = sort'
                      }  in
                    let env' = push_bvs e0 (bv' :: bvs)  in
                    replace_cur
                      (let uu___96_4876 = goal  in
                       {
                         FStar_Tactics_Types.context = env';
                         FStar_Tactics_Types.witness =
                           (uu___96_4876.FStar_Tactics_Types.witness);
                         FStar_Tactics_Types.goal_ty =
                           (uu___96_4876.FStar_Tactics_Types.goal_ty);
                         FStar_Tactics_Types.opts =
                           (uu___96_4876.FStar_Tactics_Types.opts);
                         FStar_Tactics_Types.is_guard =
                           (uu___96_4876.FStar_Tactics_Types.is_guard)
                       })))
  
let (revert : Prims.unit tac) =
  bind cur_goal
    (fun goal  ->
       let uu____4884 =
         FStar_TypeChecker_Env.pop_bv goal.FStar_Tactics_Types.context  in
       match uu____4884 with
       | FStar_Pervasives_Native.None  -> fail "Cannot revert; empty context"
       | FStar_Pervasives_Native.Some (x,env') ->
           let typ' =
             let uu____4906 =
               FStar_Syntax_Syntax.mk_Total goal.FStar_Tactics_Types.goal_ty
                in
             FStar_Syntax_Util.arrow [(x, FStar_Pervasives_Native.None)]
               uu____4906
              in
           let w' =
             FStar_Syntax_Util.abs [(x, FStar_Pervasives_Native.None)]
               goal.FStar_Tactics_Types.witness FStar_Pervasives_Native.None
              in
           replace_cur
             (let uu___97_4940 = goal  in
              {
                FStar_Tactics_Types.context = env';
                FStar_Tactics_Types.witness = w';
                FStar_Tactics_Types.goal_ty = typ';
                FStar_Tactics_Types.opts =
                  (uu___97_4940.FStar_Tactics_Types.opts);
                FStar_Tactics_Types.is_guard =
                  (uu___97_4940.FStar_Tactics_Types.is_guard)
              }))
  
let (free_in :
  FStar_Syntax_Syntax.bv -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun bv  ->
    fun t  ->
      let uu____4947 = FStar_Syntax_Free.names t  in
      FStar_Util.set_mem bv uu____4947
  
let rec (clear : FStar_Syntax_Syntax.binder -> Prims.unit tac) =
  fun b  ->
    let bv = FStar_Pervasives_Native.fst b  in
    bind cur_goal
      (fun goal  ->
         mlog
           (fun uu____4963  ->
              let uu____4964 = FStar_Syntax_Print.binder_to_string b  in
              let uu____4965 =
                let uu____4966 =
                  let uu____4967 =
                    FStar_TypeChecker_Env.all_binders
                      goal.FStar_Tactics_Types.context
                     in
                  FStar_All.pipe_right uu____4967 FStar_List.length  in
                FStar_All.pipe_right uu____4966 FStar_Util.string_of_int  in
              FStar_Util.print2 "Clear of (%s), env has %s binders\n"
                uu____4964 uu____4965)
           (fun uu____4978  ->
              let uu____4979 = split_env bv goal.FStar_Tactics_Types.context
                 in
              match uu____4979 with
              | FStar_Pervasives_Native.None  ->
                  fail "Cannot clear; binder not in environment"
              | FStar_Pervasives_Native.Some (e',bvs) ->
                  let rec check bvs1 =
                    match bvs1 with
                    | [] -> ret ()
                    | bv'::bvs2 ->
                        let uu____5024 =
                          free_in bv bv'.FStar_Syntax_Syntax.sort  in
                        if uu____5024
                        then
                          let uu____5027 =
                            let uu____5028 =
                              FStar_Syntax_Print.bv_to_string bv'  in
                            FStar_Util.format1
                              "Cannot clear; binder present in the type of %s"
                              uu____5028
                             in
                          fail uu____5027
                        else check bvs2
                     in
                  let uu____5030 =
                    free_in bv goal.FStar_Tactics_Types.goal_ty  in
                  if uu____5030
                  then fail "Cannot clear; binder present in goal"
                  else
                    (let uu____5034 = check bvs  in
                     bind uu____5034
                       (fun uu____5040  ->
                          let env' = push_bvs e' bvs  in
                          let uu____5042 =
                            new_uvar "clear.witness" env'
                              goal.FStar_Tactics_Types.goal_ty
                             in
                          bind uu____5042
                            (fun ut  ->
                               let uu____5048 =
                                 do_unify goal.FStar_Tactics_Types.context
                                   goal.FStar_Tactics_Types.witness ut
                                  in
                               if uu____5048
                               then
                                 replace_cur
                                   (let uu___98_5053 = goal  in
                                    {
                                      FStar_Tactics_Types.context = env';
                                      FStar_Tactics_Types.witness = ut;
                                      FStar_Tactics_Types.goal_ty =
                                        (uu___98_5053.FStar_Tactics_Types.goal_ty);
                                      FStar_Tactics_Types.opts =
                                        (uu___98_5053.FStar_Tactics_Types.opts);
                                      FStar_Tactics_Types.is_guard =
                                        (uu___98_5053.FStar_Tactics_Types.is_guard)
                                    })
                               else
                                 fail
                                   "Cannot clear; binder appears in witness")))))
  
let (clear_top : Prims.unit tac) =
  bind cur_goal
    (fun goal  ->
       let uu____5062 =
         FStar_TypeChecker_Env.pop_bv goal.FStar_Tactics_Types.context  in
       match uu____5062 with
       | FStar_Pervasives_Native.None  -> fail "Cannot clear; empty context"
       | FStar_Pervasives_Native.Some (x,uu____5076) ->
           let uu____5081 = FStar_Syntax_Syntax.mk_binder x  in
           clear uu____5081)
  
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
           let uu___99_5097 = g  in
           {
             FStar_Tactics_Types.context = ctx';
             FStar_Tactics_Types.witness =
               (uu___99_5097.FStar_Tactics_Types.witness);
             FStar_Tactics_Types.goal_ty =
               (uu___99_5097.FStar_Tactics_Types.goal_ty);
             FStar_Tactics_Types.opts =
               (uu___99_5097.FStar_Tactics_Types.opts);
             FStar_Tactics_Types.is_guard =
               (uu___99_5097.FStar_Tactics_Types.is_guard)
           }  in
         bind dismiss (fun uu____5099  -> add_goals [g']))
  
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
           let uu___100_5115 = g  in
           {
             FStar_Tactics_Types.context = ctx';
             FStar_Tactics_Types.witness =
               (uu___100_5115.FStar_Tactics_Types.witness);
             FStar_Tactics_Types.goal_ty =
               (uu___100_5115.FStar_Tactics_Types.goal_ty);
             FStar_Tactics_Types.opts =
               (uu___100_5115.FStar_Tactics_Types.opts);
             FStar_Tactics_Types.is_guard =
               (uu___100_5115.FStar_Tactics_Types.is_guard)
           }  in
         bind dismiss (fun uu____5117  -> add_goals [g']))
  
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
            let uu____5149 = FStar_Syntax_Subst.compress t  in
            uu____5149.FStar_Syntax_Syntax.n  in
          let uu____5152 =
            if d = FStar_Tactics_Types.TopDown
            then
              f env
                (let uu___102_5158 = t  in
                 {
                   FStar_Syntax_Syntax.n = tn;
                   FStar_Syntax_Syntax.pos =
                     (uu___102_5158.FStar_Syntax_Syntax.pos);
                   FStar_Syntax_Syntax.vars =
                     (uu___102_5158.FStar_Syntax_Syntax.vars)
                 })
            else ret t  in
          bind uu____5152
            (fun t1  ->
               let tn1 =
                 let uu____5166 =
                   let uu____5167 = FStar_Syntax_Subst.compress t1  in
                   uu____5167.FStar_Syntax_Syntax.n  in
                 match uu____5166 with
                 | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
                     let ff = tac_fold_env d f env  in
                     let uu____5199 = ff hd1  in
                     bind uu____5199
                       (fun hd2  ->
                          let fa uu____5219 =
                            match uu____5219 with
                            | (a,q) ->
                                let uu____5232 = ff a  in
                                bind uu____5232 (fun a1  -> ret (a1, q))
                             in
                          let uu____5245 = mapM fa args  in
                          bind uu____5245
                            (fun args1  ->
                               ret (FStar_Syntax_Syntax.Tm_app (hd2, args1))))
                 | FStar_Syntax_Syntax.Tm_abs (bs,t2,k) ->
                     let uu____5305 = FStar_Syntax_Subst.open_term bs t2  in
                     (match uu____5305 with
                      | (bs1,t') ->
                          let uu____5314 =
                            let uu____5317 =
                              FStar_TypeChecker_Env.push_binders env bs1  in
                            tac_fold_env d f uu____5317 t'  in
                          bind uu____5314
                            (fun t''  ->
                               let uu____5321 =
                                 let uu____5322 =
                                   let uu____5339 =
                                     FStar_Syntax_Subst.close_binders bs1  in
                                   let uu____5340 =
                                     FStar_Syntax_Subst.close bs1 t''  in
                                   (uu____5339, uu____5340, k)  in
                                 FStar_Syntax_Syntax.Tm_abs uu____5322  in
                               ret uu____5321))
                 | FStar_Syntax_Syntax.Tm_arrow (bs,k) -> ret tn
                 | uu____5361 -> ret tn  in
               bind tn1
                 (fun tn2  ->
                    let t' =
                      let uu___101_5368 = t1  in
                      {
                        FStar_Syntax_Syntax.n = tn2;
                        FStar_Syntax_Syntax.pos =
                          (uu___101_5368.FStar_Syntax_Syntax.pos);
                        FStar_Syntax_Syntax.vars =
                          (uu___101_5368.FStar_Syntax_Syntax.vars)
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
            let uu____5397 = FStar_TypeChecker_TcTerm.tc_term env t  in
            match uu____5397 with
            | (t1,lcomp,g) ->
                let uu____5409 =
                  (let uu____5412 =
                     FStar_Syntax_Util.is_pure_or_ghost_lcomp lcomp  in
                   Prims.op_Negation uu____5412) ||
                    (let uu____5414 = FStar_TypeChecker_Rel.is_trivial g  in
                     Prims.op_Negation uu____5414)
                   in
                if uu____5409
                then ret t1
                else
                  (let rewrite_eq =
                     let typ = lcomp.FStar_Syntax_Syntax.res_typ  in
                     let uu____5424 = new_uvar "pointwise_rec" env typ  in
                     bind uu____5424
                       (fun ut  ->
                          log ps
                            (fun uu____5435  ->
                               let uu____5436 =
                                 FStar_Syntax_Print.term_to_string t1  in
                               let uu____5437 =
                                 FStar_Syntax_Print.term_to_string ut  in
                               FStar_Util.print2
                                 "Pointwise_rec: making equality\n\t%s ==\n\t%s\n"
                                 uu____5436 uu____5437);
                          (let uu____5438 =
                             let uu____5441 =
                               let uu____5442 =
                                 FStar_TypeChecker_TcTerm.universe_of env typ
                                  in
                               FStar_Syntax_Util.mk_eq2 uu____5442 typ t1 ut
                                in
                             add_irrelevant_goal "pointwise_rec equation" env
                               uu____5441 opts
                              in
                           bind uu____5438
                             (fun uu____5445  ->
                                let uu____5446 =
                                  bind tau
                                    (fun uu____5452  ->
                                       let ut1 =
                                         FStar_TypeChecker_Normalize.reduce_uvar_solutions
                                           env ut
                                          in
                                       log ps
                                         (fun uu____5458  ->
                                            let uu____5459 =
                                              FStar_Syntax_Print.term_to_string
                                                t1
                                               in
                                            let uu____5460 =
                                              FStar_Syntax_Print.term_to_string
                                                ut1
                                               in
                                            FStar_Util.print2
                                              "Pointwise_rec: succeeded rewriting\n\t%s to\n\t%s\n"
                                              uu____5459 uu____5460);
                                       ret ut1)
                                   in
                                focus uu____5446)))
                      in
                   let uu____5461 = trytac' rewrite_eq  in
                   bind uu____5461
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
          let uu____5609 = FStar_Syntax_Subst.compress t  in
          maybe_continue ctrl uu____5609
            (fun t1  ->
               let uu____5613 =
                 f env
                   (let uu___105_5622 = t1  in
                    {
                      FStar_Syntax_Syntax.n = (t1.FStar_Syntax_Syntax.n);
                      FStar_Syntax_Syntax.pos =
                        (uu___105_5622.FStar_Syntax_Syntax.pos);
                      FStar_Syntax_Syntax.vars =
                        (uu___105_5622.FStar_Syntax_Syntax.vars)
                    })
                  in
               bind uu____5613
                 (fun uu____5634  ->
                    match uu____5634 with
                    | (t2,ctrl1) ->
                        maybe_continue ctrl1 t2
                          (fun t3  ->
                             let uu____5653 =
                               let uu____5654 =
                                 FStar_Syntax_Subst.compress t3  in
                               uu____5654.FStar_Syntax_Syntax.n  in
                             match uu____5653 with
                             | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
                                 let uu____5687 =
                                   ctrl_tac_fold f env ctrl1 hd1  in
                                 bind uu____5687
                                   (fun uu____5712  ->
                                      match uu____5712 with
                                      | (hd2,ctrl2) ->
                                          let ctrl3 = keep_going ctrl2  in
                                          let uu____5728 =
                                            ctrl_tac_fold_args f env ctrl3
                                              args
                                             in
                                          bind uu____5728
                                            (fun uu____5755  ->
                                               match uu____5755 with
                                               | (args1,ctrl4) ->
                                                   ret
                                                     ((let uu___103_5785 = t3
                                                          in
                                                       {
                                                         FStar_Syntax_Syntax.n
                                                           =
                                                           (FStar_Syntax_Syntax.Tm_app
                                                              (hd2, args1));
                                                         FStar_Syntax_Syntax.pos
                                                           =
                                                           (uu___103_5785.FStar_Syntax_Syntax.pos);
                                                         FStar_Syntax_Syntax.vars
                                                           =
                                                           (uu___103_5785.FStar_Syntax_Syntax.vars)
                                                       }), ctrl4)))
                             | FStar_Syntax_Syntax.Tm_abs (bs,t4,k) ->
                                 let uu____5811 =
                                   FStar_Syntax_Subst.open_term bs t4  in
                                 (match uu____5811 with
                                  | (bs1,t') ->
                                      let uu____5826 =
                                        let uu____5833 =
                                          FStar_TypeChecker_Env.push_binders
                                            env bs1
                                           in
                                        ctrl_tac_fold f uu____5833 ctrl1 t'
                                         in
                                      bind uu____5826
                                        (fun uu____5851  ->
                                           match uu____5851 with
                                           | (t'',ctrl2) ->
                                               let uu____5866 =
                                                 let uu____5873 =
                                                   let uu___104_5876 = t4  in
                                                   let uu____5879 =
                                                     let uu____5880 =
                                                       let uu____5897 =
                                                         FStar_Syntax_Subst.close_binders
                                                           bs1
                                                          in
                                                       let uu____5898 =
                                                         FStar_Syntax_Subst.close
                                                           bs1 t''
                                                          in
                                                       (uu____5897,
                                                         uu____5898, k)
                                                        in
                                                     FStar_Syntax_Syntax.Tm_abs
                                                       uu____5880
                                                      in
                                                   {
                                                     FStar_Syntax_Syntax.n =
                                                       uu____5879;
                                                     FStar_Syntax_Syntax.pos
                                                       =
                                                       (uu___104_5876.FStar_Syntax_Syntax.pos);
                                                     FStar_Syntax_Syntax.vars
                                                       =
                                                       (uu___104_5876.FStar_Syntax_Syntax.vars)
                                                   }  in
                                                 (uu____5873, ctrl2)  in
                                               ret uu____5866))
                             | FStar_Syntax_Syntax.Tm_arrow (bs,k) ->
                                 ret (t3, ctrl1)
                             | uu____5931 -> ret (t3, ctrl1))))

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
              let uu____5982 = ctrl_tac_fold f env ctrl t  in
              bind uu____5982
                (fun uu____6010  ->
                   match uu____6010 with
                   | (t1,ctrl1) ->
                       let uu____6029 = ctrl_tac_fold_args f env ctrl1 ts1
                          in
                       bind uu____6029
                         (fun uu____6060  ->
                            match uu____6060 with
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
              let uu____6144 =
                let uu____6151 =
                  add_irrelevant_goal "dummy" env FStar_Syntax_Util.t_true
                    opts
                   in
                bind uu____6151
                  (fun uu____6160  ->
                     let uu____6161 = ctrl t1  in
                     bind uu____6161
                       (fun res  -> bind trivial (fun uu____6188  -> ret res)))
                 in
              bind uu____6144
                (fun uu____6204  ->
                   match uu____6204 with
                   | (should_rewrite,ctrl1) ->
                       if Prims.op_Negation should_rewrite
                       then ret (t1, ctrl1)
                       else
                         (let uu____6228 =
                            FStar_TypeChecker_TcTerm.tc_term env t1  in
                          match uu____6228 with
                          | (t2,lcomp,g) ->
                              let uu____6244 =
                                (let uu____6247 =
                                   FStar_Syntax_Util.is_pure_or_ghost_lcomp
                                     lcomp
                                    in
                                 Prims.op_Negation uu____6247) ||
                                  (let uu____6249 =
                                     FStar_TypeChecker_Rel.is_trivial g  in
                                   Prims.op_Negation uu____6249)
                                 in
                              if uu____6244
                              then ret (t2, globalStop)
                              else
                                (let typ = lcomp.FStar_Syntax_Syntax.res_typ
                                    in
                                 let uu____6264 =
                                   new_uvar "pointwise_rec" env typ  in
                                 bind uu____6264
                                   (fun ut  ->
                                      log ps
                                        (fun uu____6279  ->
                                           let uu____6280 =
                                             FStar_Syntax_Print.term_to_string
                                               t2
                                              in
                                           let uu____6281 =
                                             FStar_Syntax_Print.term_to_string
                                               ut
                                              in
                                           FStar_Util.print2
                                             "Pointwise_rec: making equality\n\t%s ==\n\t%s\n"
                                             uu____6280 uu____6281);
                                      (let uu____6282 =
                                         let uu____6285 =
                                           let uu____6286 =
                                             FStar_TypeChecker_TcTerm.universe_of
                                               env typ
                                              in
                                           FStar_Syntax_Util.mk_eq2
                                             uu____6286 typ t2 ut
                                            in
                                         add_irrelevant_goal
                                           "rewrite_rec equation" env
                                           uu____6285 opts
                                          in
                                       bind uu____6282
                                         (fun uu____6293  ->
                                            let uu____6294 =
                                              bind rewriter
                                                (fun uu____6308  ->
                                                   let ut1 =
                                                     FStar_TypeChecker_Normalize.reduce_uvar_solutions
                                                       env ut
                                                      in
                                                   log ps
                                                     (fun uu____6314  ->
                                                        let uu____6315 =
                                                          FStar_Syntax_Print.term_to_string
                                                            t2
                                                           in
                                                        let uu____6316 =
                                                          FStar_Syntax_Print.term_to_string
                                                            ut1
                                                           in
                                                        FStar_Util.print2
                                                          "rewrite_rec: succeeded rewriting\n\t%s to\n\t%s\n"
                                                          uu____6315
                                                          uu____6316);
                                                   ret (ut1, ctrl1))
                                               in
                                            focus uu____6294))))))
  
let (topdown_rewrite :
  (FStar_Syntax_Syntax.term ->
     (Prims.bool,FStar_BigInt.t) FStar_Pervasives_Native.tuple2 tac)
    -> Prims.unit tac -> Prims.unit tac)
  =
  fun ctrl  ->
    fun rewriter  ->
      bind get
        (fun ps  ->
           let uu____6360 =
             match ps.FStar_Tactics_Types.goals with
             | g::gs -> (g, gs)
             | [] -> failwith "Pointwise: no goals"  in
           match uu____6360 with
           | (g,gs) ->
               let gt1 = g.FStar_Tactics_Types.goal_ty  in
               (log ps
                  (fun uu____6397  ->
                     let uu____6398 = FStar_Syntax_Print.term_to_string gt1
                        in
                     FStar_Util.print1 "Pointwise starting with %s\n"
                       uu____6398);
                bind dismiss_all
                  (fun uu____6401  ->
                     let uu____6402 =
                       ctrl_tac_fold
                         (rewrite_rec ps ctrl rewriter
                            g.FStar_Tactics_Types.opts)
                         g.FStar_Tactics_Types.context keepGoing gt1
                        in
                     bind uu____6402
                       (fun uu____6420  ->
                          match uu____6420 with
                          | (gt',uu____6428) ->
                              (log ps
                                 (fun uu____6432  ->
                                    let uu____6433 =
                                      FStar_Syntax_Print.term_to_string gt'
                                       in
                                    FStar_Util.print1
                                      "Pointwise seems to have succeded with %s\n"
                                      uu____6433);
                               (let uu____6434 = push_goals gs  in
                                bind uu____6434
                                  (fun uu____6438  ->
                                     add_goals
                                       [(let uu___106_6440 = g  in
                                         {
                                           FStar_Tactics_Types.context =
                                             (uu___106_6440.FStar_Tactics_Types.context);
                                           FStar_Tactics_Types.witness =
                                             (uu___106_6440.FStar_Tactics_Types.witness);
                                           FStar_Tactics_Types.goal_ty = gt';
                                           FStar_Tactics_Types.opts =
                                             (uu___106_6440.FStar_Tactics_Types.opts);
                                           FStar_Tactics_Types.is_guard =
                                             (uu___106_6440.FStar_Tactics_Types.is_guard)
                                         })])))))))
  
let (pointwise :
  FStar_Tactics_Types.direction -> Prims.unit tac -> Prims.unit tac) =
  fun d  ->
    fun tau  ->
      bind get
        (fun ps  ->
           let uu____6462 =
             match ps.FStar_Tactics_Types.goals with
             | g::gs -> (g, gs)
             | [] -> failwith "Pointwise: no goals"  in
           match uu____6462 with
           | (g,gs) ->
               let gt1 = g.FStar_Tactics_Types.goal_ty  in
               (log ps
                  (fun uu____6499  ->
                     let uu____6500 = FStar_Syntax_Print.term_to_string gt1
                        in
                     FStar_Util.print1 "Pointwise starting with %s\n"
                       uu____6500);
                bind dismiss_all
                  (fun uu____6503  ->
                     let uu____6504 =
                       tac_fold_env d
                         (pointwise_rec ps tau g.FStar_Tactics_Types.opts)
                         g.FStar_Tactics_Types.context gt1
                        in
                     bind uu____6504
                       (fun gt'  ->
                          log ps
                            (fun uu____6514  ->
                               let uu____6515 =
                                 FStar_Syntax_Print.term_to_string gt'  in
                               FStar_Util.print1
                                 "Pointwise seems to have succeded with %s\n"
                                 uu____6515);
                          (let uu____6516 = push_goals gs  in
                           bind uu____6516
                             (fun uu____6520  ->
                                add_goals
                                  [(let uu___107_6522 = g  in
                                    {
                                      FStar_Tactics_Types.context =
                                        (uu___107_6522.FStar_Tactics_Types.context);
                                      FStar_Tactics_Types.witness =
                                        (uu___107_6522.FStar_Tactics_Types.witness);
                                      FStar_Tactics_Types.goal_ty = gt';
                                      FStar_Tactics_Types.opts =
                                        (uu___107_6522.FStar_Tactics_Types.opts);
                                      FStar_Tactics_Types.is_guard =
                                        (uu___107_6522.FStar_Tactics_Types.is_guard)
                                    })]))))))
  
let (trefl : Prims.unit tac) =
  bind cur_goal
    (fun g  ->
       let uu____6544 =
         FStar_Syntax_Util.un_squash g.FStar_Tactics_Types.goal_ty  in
       match uu____6544 with
       | FStar_Pervasives_Native.Some t ->
           let uu____6556 = FStar_Syntax_Util.head_and_args' t  in
           (match uu____6556 with
            | (hd1,args) ->
                let uu____6589 =
                  let uu____6602 =
                    let uu____6603 = FStar_Syntax_Util.un_uinst hd1  in
                    uu____6603.FStar_Syntax_Syntax.n  in
                  (uu____6602, args)  in
                (match uu____6589 with
                 | (FStar_Syntax_Syntax.Tm_fvar
                    fv,uu____6617::(l,uu____6619)::(r,uu____6621)::[]) when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.eq2_lid
                     ->
                     let uu____6668 =
                       let uu____6669 =
                         do_unify g.FStar_Tactics_Types.context l r  in
                       Prims.op_Negation uu____6669  in
                     if uu____6668
                     then
                       let uu____6672 = tts g.FStar_Tactics_Types.context l
                          in
                       let uu____6673 = tts g.FStar_Tactics_Types.context r
                          in
                       fail2 "trefl: not a trivial equality (%s vs %s)"
                         uu____6672 uu____6673
                     else solve g FStar_Syntax_Util.exp_unit
                 | (hd2,uu____6676) ->
                     let uu____6693 = tts g.FStar_Tactics_Types.context t  in
                     fail1 "trefl: not an equality (%s)" uu____6693))
       | FStar_Pervasives_Native.None  -> fail "not an irrelevant goal")
  
let (dup : Prims.unit tac) =
  bind cur_goal
    (fun g  ->
       let uu____6703 =
         new_uvar "dup" g.FStar_Tactics_Types.context
           g.FStar_Tactics_Types.goal_ty
          in
       bind uu____6703
         (fun u  ->
            let g' =
              let uu___108_6710 = g  in
              {
                FStar_Tactics_Types.context =
                  (uu___108_6710.FStar_Tactics_Types.context);
                FStar_Tactics_Types.witness = u;
                FStar_Tactics_Types.goal_ty =
                  (uu___108_6710.FStar_Tactics_Types.goal_ty);
                FStar_Tactics_Types.opts =
                  (uu___108_6710.FStar_Tactics_Types.opts);
                FStar_Tactics_Types.is_guard =
                  (uu___108_6710.FStar_Tactics_Types.is_guard)
              }  in
            bind dismiss
              (fun uu____6713  ->
                 let uu____6714 =
                   let uu____6717 =
                     let uu____6718 =
                       FStar_TypeChecker_TcTerm.universe_of
                         g.FStar_Tactics_Types.context
                         g.FStar_Tactics_Types.goal_ty
                        in
                     FStar_Syntax_Util.mk_eq2 uu____6718
                       g.FStar_Tactics_Types.goal_ty u
                       g.FStar_Tactics_Types.witness
                      in
                   add_irrelevant_goal "dup equation"
                     g.FStar_Tactics_Types.context uu____6717
                     g.FStar_Tactics_Types.opts
                    in
                 bind uu____6714
                   (fun uu____6721  ->
                      let uu____6722 = add_goals [g']  in
                      bind uu____6722 (fun uu____6726  -> ret ())))))
  
let (flip : Prims.unit tac) =
  bind get
    (fun ps  ->
       match ps.FStar_Tactics_Types.goals with
       | g1::g2::gs ->
           set
             (let uu___109_6745 = ps  in
              {
                FStar_Tactics_Types.main_context =
                  (uu___109_6745.FStar_Tactics_Types.main_context);
                FStar_Tactics_Types.main_goal =
                  (uu___109_6745.FStar_Tactics_Types.main_goal);
                FStar_Tactics_Types.all_implicits =
                  (uu___109_6745.FStar_Tactics_Types.all_implicits);
                FStar_Tactics_Types.goals = (g2 :: g1 :: gs);
                FStar_Tactics_Types.smt_goals =
                  (uu___109_6745.FStar_Tactics_Types.smt_goals);
                FStar_Tactics_Types.depth =
                  (uu___109_6745.FStar_Tactics_Types.depth);
                FStar_Tactics_Types.__dump =
                  (uu___109_6745.FStar_Tactics_Types.__dump);
                FStar_Tactics_Types.psc =
                  (uu___109_6745.FStar_Tactics_Types.psc);
                FStar_Tactics_Types.entry_range =
                  (uu___109_6745.FStar_Tactics_Types.entry_range)
              })
       | uu____6746 -> fail "flip: less than 2 goals")
  
let (later : Prims.unit tac) =
  bind get
    (fun ps  ->
       match ps.FStar_Tactics_Types.goals with
       | [] -> ret ()
       | g::gs ->
           set
             (let uu___110_6763 = ps  in
              {
                FStar_Tactics_Types.main_context =
                  (uu___110_6763.FStar_Tactics_Types.main_context);
                FStar_Tactics_Types.main_goal =
                  (uu___110_6763.FStar_Tactics_Types.main_goal);
                FStar_Tactics_Types.all_implicits =
                  (uu___110_6763.FStar_Tactics_Types.all_implicits);
                FStar_Tactics_Types.goals = (FStar_List.append gs [g]);
                FStar_Tactics_Types.smt_goals =
                  (uu___110_6763.FStar_Tactics_Types.smt_goals);
                FStar_Tactics_Types.depth =
                  (uu___110_6763.FStar_Tactics_Types.depth);
                FStar_Tactics_Types.__dump =
                  (uu___110_6763.FStar_Tactics_Types.__dump);
                FStar_Tactics_Types.psc =
                  (uu___110_6763.FStar_Tactics_Types.psc);
                FStar_Tactics_Types.entry_range =
                  (uu___110_6763.FStar_Tactics_Types.entry_range)
              }))
  
let (qed : Prims.unit tac) =
  bind get
    (fun ps  ->
       match ps.FStar_Tactics_Types.goals with
       | [] -> ret ()
       | uu____6772 -> fail "Not done!")
  
let (cases :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 tac)
  =
  fun t  ->
    let uu____6790 =
      bind cur_goal
        (fun g  ->
           let uu____6804 = __tc g.FStar_Tactics_Types.context t  in
           bind uu____6804
             (fun uu____6840  ->
                match uu____6840 with
                | (t1,typ,guard) ->
                    let uu____6856 = FStar_Syntax_Util.head_and_args typ  in
                    (match uu____6856 with
                     | (hd1,args) ->
                         let uu____6899 =
                           let uu____6912 =
                             let uu____6913 = FStar_Syntax_Util.un_uinst hd1
                                in
                             uu____6913.FStar_Syntax_Syntax.n  in
                           (uu____6912, args)  in
                         (match uu____6899 with
                          | (FStar_Syntax_Syntax.Tm_fvar
                             fv,(p,uu____6932)::(q,uu____6934)::[]) when
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
                                let uu___111_6972 = g  in
                                let uu____6973 =
                                  FStar_TypeChecker_Env.push_bv
                                    g.FStar_Tactics_Types.context v_p
                                   in
                                {
                                  FStar_Tactics_Types.context = uu____6973;
                                  FStar_Tactics_Types.witness =
                                    (uu___111_6972.FStar_Tactics_Types.witness);
                                  FStar_Tactics_Types.goal_ty =
                                    (uu___111_6972.FStar_Tactics_Types.goal_ty);
                                  FStar_Tactics_Types.opts =
                                    (uu___111_6972.FStar_Tactics_Types.opts);
                                  FStar_Tactics_Types.is_guard =
                                    (uu___111_6972.FStar_Tactics_Types.is_guard)
                                }  in
                              let g2 =
                                let uu___112_6975 = g  in
                                let uu____6976 =
                                  FStar_TypeChecker_Env.push_bv
                                    g.FStar_Tactics_Types.context v_q
                                   in
                                {
                                  FStar_Tactics_Types.context = uu____6976;
                                  FStar_Tactics_Types.witness =
                                    (uu___112_6975.FStar_Tactics_Types.witness);
                                  FStar_Tactics_Types.goal_ty =
                                    (uu___112_6975.FStar_Tactics_Types.goal_ty);
                                  FStar_Tactics_Types.opts =
                                    (uu___112_6975.FStar_Tactics_Types.opts);
                                  FStar_Tactics_Types.is_guard =
                                    (uu___112_6975.FStar_Tactics_Types.is_guard)
                                }  in
                              bind dismiss
                                (fun uu____6983  ->
                                   let uu____6984 = add_goals [g1; g2]  in
                                   bind uu____6984
                                     (fun uu____6993  ->
                                        let uu____6994 =
                                          let uu____6999 =
                                            FStar_Syntax_Syntax.bv_to_name
                                              v_p
                                             in
                                          let uu____7000 =
                                            FStar_Syntax_Syntax.bv_to_name
                                              v_q
                                             in
                                          (uu____6999, uu____7000)  in
                                        ret uu____6994))
                          | uu____7005 ->
                              let uu____7018 =
                                tts g.FStar_Tactics_Types.context typ  in
                              fail1 "Not a disjunction: %s" uu____7018))))
       in
    FStar_All.pipe_left (wrap_err "cases") uu____6790
  
let (set_options : Prims.string -> Prims.unit tac) =
  fun s  ->
    bind cur_goal
      (fun g  ->
         FStar_Options.push ();
         (let uu____7056 = FStar_Util.smap_copy g.FStar_Tactics_Types.opts
             in
          FStar_Options.set uu____7056);
         (let res = FStar_Options.set_options FStar_Options.Set s  in
          let opts' = FStar_Options.peek ()  in
          FStar_Options.pop ();
          (match res with
           | FStar_Getopt.Success  ->
               let g' =
                 let uu___113_7063 = g  in
                 {
                   FStar_Tactics_Types.context =
                     (uu___113_7063.FStar_Tactics_Types.context);
                   FStar_Tactics_Types.witness =
                     (uu___113_7063.FStar_Tactics_Types.witness);
                   FStar_Tactics_Types.goal_ty =
                     (uu___113_7063.FStar_Tactics_Types.goal_ty);
                   FStar_Tactics_Types.opts = opts';
                   FStar_Tactics_Types.is_guard =
                     (uu___113_7063.FStar_Tactics_Types.is_guard)
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
      let uu____7107 =
        bind cur_goal
          (fun goal  ->
             let env =
               FStar_TypeChecker_Env.set_expected_typ
                 goal.FStar_Tactics_Types.context ty
                in
             let uu____7115 = __tc env tm  in
             bind uu____7115
               (fun uu____7135  ->
                  match uu____7135 with
                  | (tm1,typ,guard) ->
                      (FStar_TypeChecker_Rel.force_trivial_guard env guard;
                       ret tm1)))
         in
      FStar_All.pipe_left (wrap_err "unquote") uu____7107
  
let (uvar_env :
  env ->
    FStar_Syntax_Syntax.typ FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.term tac)
  =
  fun env  ->
    fun ty  ->
      let uu____7166 =
        match ty with
        | FStar_Pervasives_Native.Some ty1 -> ret ty1
        | FStar_Pervasives_Native.None  ->
            let uu____7172 =
              let uu____7173 = FStar_Syntax_Util.type_u ()  in
              FStar_All.pipe_left FStar_Pervasives_Native.fst uu____7173  in
            new_uvar "uvar_env.2" env uu____7172
         in
      bind uu____7166
        (fun typ  ->
           let uu____7185 = new_uvar "uvar_env" env typ  in
           bind uu____7185 (fun t  -> ret t))
  
let (unshelve : FStar_Syntax_Syntax.term -> Prims.unit tac) =
  fun t  ->
    let uu____7197 =
      bind cur_goal
        (fun goal  ->
           let uu____7203 = __tc goal.FStar_Tactics_Types.context t  in
           bind uu____7203
             (fun uu____7223  ->
                match uu____7223 with
                | (t1,typ,guard) ->
                    let uu____7235 =
                      must_trivial goal.FStar_Tactics_Types.context guard  in
                    bind uu____7235
                      (fun uu____7240  ->
                         let uu____7241 =
                           let uu____7244 =
                             let uu___114_7245 = goal  in
                             let uu____7246 =
                               bnorm goal.FStar_Tactics_Types.context t1  in
                             let uu____7247 =
                               bnorm goal.FStar_Tactics_Types.context typ  in
                             {
                               FStar_Tactics_Types.context =
                                 (uu___114_7245.FStar_Tactics_Types.context);
                               FStar_Tactics_Types.witness = uu____7246;
                               FStar_Tactics_Types.goal_ty = uu____7247;
                               FStar_Tactics_Types.opts =
                                 (uu___114_7245.FStar_Tactics_Types.opts);
                               FStar_Tactics_Types.is_guard = false
                             }  in
                           [uu____7244]  in
                         add_goals uu____7241)))
       in
    FStar_All.pipe_left (wrap_err "unshelve") uu____7197
  
let (unify :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool tac) =
  fun t1  ->
    fun t2  ->
      bind get
        (fun ps  ->
           let uu____7265 =
             do_unify ps.FStar_Tactics_Types.main_context t1 t2  in
           ret uu____7265)
  
let (launch_process :
  Prims.string -> Prims.string -> Prims.string -> Prims.string tac) =
  fun prog  ->
    fun args  ->
      fun input  ->
        bind idtac
          (fun uu____7282  ->
             let uu____7283 = FStar_Options.unsafe_tactic_exec ()  in
             if uu____7283
             then
               let s =
                 FStar_Util.launch_process true "tactic_launch" prog args
                   input (fun uu____7289  -> fun uu____7290  -> false)
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
        (fun uu____7304  ->
           let uu____7305 =
             FStar_Syntax_Syntax.gen_bv nm FStar_Pervasives_Native.None t  in
           ret uu____7305)
  
let (goal_of_goal_ty :
  env ->
    FStar_Syntax_Syntax.typ ->
      (FStar_Tactics_Types.goal,FStar_TypeChecker_Env.guard_t)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun typ  ->
      let uu____7320 =
        FStar_TypeChecker_Util.new_implicit_var "proofstate_of_goal_ty"
          typ.FStar_Syntax_Syntax.pos env typ
         in
      match uu____7320 with
      | (u,uu____7338,g_u) ->
          let g =
            let uu____7353 = FStar_Options.peek ()  in
            {
              FStar_Tactics_Types.context = env;
              FStar_Tactics_Types.witness = u;
              FStar_Tactics_Types.goal_ty = typ;
              FStar_Tactics_Types.opts = uu____7353;
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
      let uu____7364 = goal_of_goal_ty env typ  in
      match uu____7364 with
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
              FStar_Tactics_Types.entry_range = FStar_Range.dummyRange
            }  in
          (ps, (g.FStar_Tactics_Types.witness))
  