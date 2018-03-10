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
             (uu___61_1005.FStar_Tactics_Types.entry_range)
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
              (uu___62_1037.FStar_Tactics_Types.entry_range)
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
                (uu___63_1176.FStar_Tactics_Types.entry_range)
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
                (uu___64_1194.FStar_Tactics_Types.entry_range)
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
                (uu___65_1212.FStar_Tactics_Types.entry_range)
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
                (uu___66_1230.FStar_Tactics_Types.entry_range)
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
                (uu___67_1251.FStar_Tactics_Types.entry_range)
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
  
let (must_trivial :
  Prims.string -> env -> FStar_TypeChecker_Env.guard_t -> Prims.unit tac) =
  fun s  ->
    fun e  ->
      fun g  ->
        try
          let uu____1508 =
            let uu____1509 =
              let uu____1510 =
                FStar_TypeChecker_Rel.discharge_guard_no_smt e g  in
              FStar_All.pipe_left FStar_TypeChecker_Rel.is_trivial uu____1510
               in
            Prims.op_Negation uu____1509  in
          if uu____1508
          then
            mlog
              (fun uu____1515  ->
                 let uu____1516 = FStar_TypeChecker_Rel.guard_to_string e g
                    in
                 FStar_Util.print1 "guard = %s\n" uu____1516)
              (fun uu____1518  -> fail1 "got non-trivial guard (%s)" s)
          else ret ()
        with
        | uu____1525 ->
            mlog
              (fun uu____1528  ->
                 let uu____1529 = FStar_TypeChecker_Rel.guard_to_string e g
                    in
                 FStar_Util.print1 "guard = %s\n" uu____1529)
              (fun uu____1531  -> fail1 "got non-trivial guard (%s)" s)
  
let (tc : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.typ tac) =
  fun t  ->
    let uu____1539 =
      bind cur_goal
        (fun goal  ->
           let uu____1545 = __tc goal.FStar_Tactics_Types.context t  in
           bind uu____1545
             (fun uu____1565  ->
                match uu____1565 with
                | (t1,typ,guard) ->
                    let uu____1577 =
                      must_trivial "tc" goal.FStar_Tactics_Types.context
                        guard
                       in
                    bind uu____1577 (fun uu____1581  -> ret typ)))
       in
    FStar_All.pipe_left (wrap_err "tc") uu____1539
  
let (add_irrelevant_goal :
  Prims.string ->
    env ->
      FStar_Syntax_Syntax.typ -> FStar_Options.optionstate -> Prims.unit tac)
  =
  fun reason  ->
    fun env  ->
      fun phi  ->
        fun opts  ->
          let uu____1602 = mk_irrelevant_goal reason env phi opts  in
          bind uu____1602 (fun goal  -> add_goals [goal])
  
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
       let uu____1624 =
         istrivial goal.FStar_Tactics_Types.context
           goal.FStar_Tactics_Types.goal_ty
          in
       if uu____1624
       then solve goal FStar_Syntax_Util.exp_unit
       else
         (let uu____1628 =
            tts goal.FStar_Tactics_Types.context
              goal.FStar_Tactics_Types.goal_ty
             in
          fail1 "Not a trivial goal: %s" uu____1628))
  
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
          let uu____1645 =
            let uu____1646 = FStar_TypeChecker_Rel.simplify_guard e g  in
            uu____1646.FStar_TypeChecker_Env.guard_f  in
          match uu____1645 with
          | FStar_TypeChecker_Common.Trivial  -> ret ()
          | FStar_TypeChecker_Common.NonTrivial f ->
              let uu____1650 = istrivial e f  in
              if uu____1650
              then ret ()
              else
                (let uu____1654 = mk_irrelevant_goal reason e f opts  in
                 bind uu____1654
                   (fun goal  ->
                      let goal1 =
                        let uu___72_1661 = goal  in
                        {
                          FStar_Tactics_Types.context =
                            (uu___72_1661.FStar_Tactics_Types.context);
                          FStar_Tactics_Types.witness =
                            (uu___72_1661.FStar_Tactics_Types.witness);
                          FStar_Tactics_Types.goal_ty =
                            (uu___72_1661.FStar_Tactics_Types.goal_ty);
                          FStar_Tactics_Types.opts =
                            (uu___72_1661.FStar_Tactics_Types.opts);
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
          let uu____1682 =
            let uu____1683 = FStar_TypeChecker_Rel.simplify_guard e g  in
            uu____1683.FStar_TypeChecker_Env.guard_f  in
          match uu____1682 with
          | FStar_TypeChecker_Common.Trivial  ->
              ret FStar_Pervasives_Native.None
          | FStar_TypeChecker_Common.NonTrivial f ->
              let uu____1691 = istrivial e f  in
              if uu____1691
              then ret FStar_Pervasives_Native.None
              else
                (let uu____1699 = mk_irrelevant_goal reason e f opts  in
                 bind uu____1699
                   (fun goal  ->
                      ret
                        (FStar_Pervasives_Native.Some
                           (let uu___73_1709 = goal  in
                            {
                              FStar_Tactics_Types.context =
                                (uu___73_1709.FStar_Tactics_Types.context);
                              FStar_Tactics_Types.witness =
                                (uu___73_1709.FStar_Tactics_Types.witness);
                              FStar_Tactics_Types.goal_ty =
                                (uu___73_1709.FStar_Tactics_Types.goal_ty);
                              FStar_Tactics_Types.opts =
                                (uu___73_1709.FStar_Tactics_Types.opts);
                              FStar_Tactics_Types.is_guard = true
                            }))))
  
let (smt : Prims.unit tac) =
  bind cur_goal
    (fun g  ->
       let uu____1717 = is_irrelevant g  in
       if uu____1717
       then bind dismiss (fun uu____1721  -> add_smt_goals [g])
       else
         (let uu____1723 =
            tts g.FStar_Tactics_Types.context g.FStar_Tactics_Types.goal_ty
             in
          fail1 "goal is not irrelevant: cannot dispatch to smt (%s)"
            uu____1723))
  
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
             let uu____1764 =
               try
                 let uu____1798 =
                   let uu____1807 = FStar_BigInt.to_int_fs n1  in
                   FStar_List.splitAt uu____1807 p.FStar_Tactics_Types.goals
                    in
                 ret uu____1798
               with | uu____1829 -> fail "divide: not enough goals"  in
             bind uu____1764
               (fun uu____1856  ->
                  match uu____1856 with
                  | (lgs,rgs) ->
                      let lp =
                        let uu___74_1882 = p  in
                        {
                          FStar_Tactics_Types.main_context =
                            (uu___74_1882.FStar_Tactics_Types.main_context);
                          FStar_Tactics_Types.main_goal =
                            (uu___74_1882.FStar_Tactics_Types.main_goal);
                          FStar_Tactics_Types.all_implicits =
                            (uu___74_1882.FStar_Tactics_Types.all_implicits);
                          FStar_Tactics_Types.goals = lgs;
                          FStar_Tactics_Types.smt_goals = [];
                          FStar_Tactics_Types.depth =
                            (uu___74_1882.FStar_Tactics_Types.depth);
                          FStar_Tactics_Types.__dump =
                            (uu___74_1882.FStar_Tactics_Types.__dump);
                          FStar_Tactics_Types.psc =
                            (uu___74_1882.FStar_Tactics_Types.psc);
                          FStar_Tactics_Types.entry_range =
                            (uu___74_1882.FStar_Tactics_Types.entry_range)
                        }  in
                      let rp =
                        let uu___75_1884 = p  in
                        {
                          FStar_Tactics_Types.main_context =
                            (uu___75_1884.FStar_Tactics_Types.main_context);
                          FStar_Tactics_Types.main_goal =
                            (uu___75_1884.FStar_Tactics_Types.main_goal);
                          FStar_Tactics_Types.all_implicits =
                            (uu___75_1884.FStar_Tactics_Types.all_implicits);
                          FStar_Tactics_Types.goals = rgs;
                          FStar_Tactics_Types.smt_goals = [];
                          FStar_Tactics_Types.depth =
                            (uu___75_1884.FStar_Tactics_Types.depth);
                          FStar_Tactics_Types.__dump =
                            (uu___75_1884.FStar_Tactics_Types.__dump);
                          FStar_Tactics_Types.psc =
                            (uu___75_1884.FStar_Tactics_Types.psc);
                          FStar_Tactics_Types.entry_range =
                            (uu___75_1884.FStar_Tactics_Types.entry_range)
                        }  in
                      let uu____1885 = set lp  in
                      bind uu____1885
                        (fun uu____1893  ->
                           bind l
                             (fun a  ->
                                bind get
                                  (fun lp'  ->
                                     let uu____1907 = set rp  in
                                     bind uu____1907
                                       (fun uu____1915  ->
                                          bind r
                                            (fun b  ->
                                               bind get
                                                 (fun rp'  ->
                                                    let p' =
                                                      let uu___76_1931 = p
                                                         in
                                                      {
                                                        FStar_Tactics_Types.main_context
                                                          =
                                                          (uu___76_1931.FStar_Tactics_Types.main_context);
                                                        FStar_Tactics_Types.main_goal
                                                          =
                                                          (uu___76_1931.FStar_Tactics_Types.main_goal);
                                                        FStar_Tactics_Types.all_implicits
                                                          =
                                                          (uu___76_1931.FStar_Tactics_Types.all_implicits);
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
                                                          (uu___76_1931.FStar_Tactics_Types.depth);
                                                        FStar_Tactics_Types.__dump
                                                          =
                                                          (uu___76_1931.FStar_Tactics_Types.__dump);
                                                        FStar_Tactics_Types.psc
                                                          =
                                                          (uu___76_1931.FStar_Tactics_Types.psc);
                                                        FStar_Tactics_Types.entry_range
                                                          =
                                                          (uu___76_1931.FStar_Tactics_Types.entry_range)
                                                      }  in
                                                    let uu____1932 = set p'
                                                       in
                                                    bind uu____1932
                                                      (fun uu____1940  ->
                                                         ret (a, b))))))))))
  
let focus : 'a . 'a tac -> 'a tac =
  fun f  ->
    let uu____1958 = divide FStar_BigInt.one f idtac  in
    bind uu____1958
      (fun uu____1971  -> match uu____1971 with | (a,()) -> ret a)
  
let rec map : 'a . 'a tac -> 'a Prims.list tac =
  fun tau  ->
    bind get
      (fun p  ->
         match p.FStar_Tactics_Types.goals with
         | [] -> ret []
         | uu____2005::uu____2006 ->
             let uu____2009 =
               let uu____2018 = map tau  in
               divide FStar_BigInt.one tau uu____2018  in
             bind uu____2009
               (fun uu____2036  ->
                  match uu____2036 with | (h,t) -> ret (h :: t)))
  
let (seq : Prims.unit tac -> Prims.unit tac -> Prims.unit tac) =
  fun t1  ->
    fun t2  ->
      let uu____2073 =
        bind t1
          (fun uu____2078  ->
             let uu____2079 = map t2  in
             bind uu____2079 (fun uu____2087  -> ret ()))
         in
      focus uu____2073
  
let (intro : FStar_Syntax_Syntax.binder tac) =
  let uu____2094 =
    bind cur_goal
      (fun goal  ->
         let uu____2103 =
           FStar_Syntax_Util.arrow_one goal.FStar_Tactics_Types.goal_ty  in
         match uu____2103 with
         | FStar_Pervasives_Native.Some (b,c) ->
             let uu____2118 =
               let uu____2119 = FStar_Syntax_Util.is_total_comp c  in
               Prims.op_Negation uu____2119  in
             if uu____2118
             then fail "Codomain is effectful"
             else
               (let env' =
                  FStar_TypeChecker_Env.push_binders
                    goal.FStar_Tactics_Types.context [b]
                   in
                let typ' = comp_to_typ c  in
                let uu____2125 = new_uvar "intro" env' typ'  in
                bind uu____2125
                  (fun u  ->
                     let uu____2131 =
                       let uu____2134 =
                         FStar_Syntax_Util.abs [b] u
                           FStar_Pervasives_Native.None
                          in
                       trysolve goal uu____2134  in
                     bind uu____2131
                       (fun bb  ->
                          if bb
                          then
                            let uu____2140 =
                              let uu____2143 =
                                let uu___79_2144 = goal  in
                                let uu____2145 = bnorm env' u  in
                                let uu____2146 = bnorm env' typ'  in
                                {
                                  FStar_Tactics_Types.context = env';
                                  FStar_Tactics_Types.witness = uu____2145;
                                  FStar_Tactics_Types.goal_ty = uu____2146;
                                  FStar_Tactics_Types.opts =
                                    (uu___79_2144.FStar_Tactics_Types.opts);
                                  FStar_Tactics_Types.is_guard =
                                    (uu___79_2144.FStar_Tactics_Types.is_guard)
                                }  in
                              replace_cur uu____2143  in
                            bind uu____2140 (fun uu____2148  -> ret b)
                          else fail "unification failed")))
         | FStar_Pervasives_Native.None  ->
             let uu____2154 =
               tts goal.FStar_Tactics_Types.context
                 goal.FStar_Tactics_Types.goal_ty
                in
             fail1 "goal is not an arrow (%s)" uu____2154)
     in
  FStar_All.pipe_left (wrap_err "intro") uu____2094 
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
       (let uu____2185 =
          FStar_Syntax_Util.arrow_one goal.FStar_Tactics_Types.goal_ty  in
        match uu____2185 with
        | FStar_Pervasives_Native.Some (b,c) ->
            let uu____2204 =
              let uu____2205 = FStar_Syntax_Util.is_total_comp c  in
              Prims.op_Negation uu____2205  in
            if uu____2204
            then fail "Codomain is effectful"
            else
              (let bv =
                 FStar_Syntax_Syntax.gen_bv "__recf"
                   FStar_Pervasives_Native.None
                   goal.FStar_Tactics_Types.goal_ty
                  in
               let bs =
                 let uu____2221 = FStar_Syntax_Syntax.mk_binder bv  in
                 [uu____2221; b]  in
               let env' =
                 FStar_TypeChecker_Env.push_binders
                   goal.FStar_Tactics_Types.context bs
                  in
               let uu____2223 =
                 let uu____2226 = comp_to_typ c  in
                 new_uvar "intro_rec" env' uu____2226  in
               bind uu____2223
                 (fun u  ->
                    let lb =
                      let uu____2241 =
                        FStar_Syntax_Util.abs [b] u
                          FStar_Pervasives_Native.None
                         in
                      FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl bv) []
                        goal.FStar_Tactics_Types.goal_ty
                        FStar_Parser_Const.effect_Tot_lid uu____2241 []
                        FStar_Range.dummyRange
                       in
                    let body = FStar_Syntax_Syntax.bv_to_name bv  in
                    let uu____2247 =
                      FStar_Syntax_Subst.close_let_rec [lb] body  in
                    match uu____2247 with
                    | (lbs,body1) ->
                        let tm =
                          FStar_Syntax_Syntax.mk
                            (FStar_Syntax_Syntax.Tm_let ((true, lbs), body1))
                            FStar_Pervasives_Native.None
                            (goal.FStar_Tactics_Types.witness).FStar_Syntax_Syntax.pos
                           in
                        let uu____2277 = trysolve goal tm  in
                        bind uu____2277
                          (fun bb  ->
                             if bb
                             then
                               let uu____2293 =
                                 let uu____2296 =
                                   let uu___80_2297 = goal  in
                                   let uu____2298 = bnorm env' u  in
                                   let uu____2299 =
                                     let uu____2300 = comp_to_typ c  in
                                     bnorm env' uu____2300  in
                                   {
                                     FStar_Tactics_Types.context = env';
                                     FStar_Tactics_Types.witness = uu____2298;
                                     FStar_Tactics_Types.goal_ty = uu____2299;
                                     FStar_Tactics_Types.opts =
                                       (uu___80_2297.FStar_Tactics_Types.opts);
                                     FStar_Tactics_Types.is_guard =
                                       (uu___80_2297.FStar_Tactics_Types.is_guard)
                                   }  in
                                 replace_cur uu____2296  in
                               bind uu____2293
                                 (fun uu____2307  ->
                                    let uu____2308 =
                                      let uu____2313 =
                                        FStar_Syntax_Syntax.mk_binder bv  in
                                      (uu____2313, b)  in
                                    ret uu____2308)
                             else fail "intro_rec: unification failed")))
        | FStar_Pervasives_Native.None  ->
            let uu____2327 =
              tts goal.FStar_Tactics_Types.context
                goal.FStar_Tactics_Types.goal_ty
               in
            fail1 "intro_rec: goal is not an arrow (%s)" uu____2327))
  
let (norm : FStar_Syntax_Embeddings.norm_step Prims.list -> Prims.unit tac) =
  fun s  ->
    bind cur_goal
      (fun goal  ->
         mlog
           (fun uu____2347  ->
              let uu____2348 =
                FStar_Syntax_Print.term_to_string
                  goal.FStar_Tactics_Types.witness
                 in
              FStar_Util.print1 "norm: witness = %s\n" uu____2348)
           (fun uu____2353  ->
              let steps =
                let uu____2357 = FStar_TypeChecker_Normalize.tr_norm_steps s
                   in
                FStar_List.append
                  [FStar_TypeChecker_Normalize.Reify;
                  FStar_TypeChecker_Normalize.UnfoldTac] uu____2357
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
                (let uu___81_2364 = goal  in
                 {
                   FStar_Tactics_Types.context =
                     (uu___81_2364.FStar_Tactics_Types.context);
                   FStar_Tactics_Types.witness = w;
                   FStar_Tactics_Types.goal_ty = t;
                   FStar_Tactics_Types.opts =
                     (uu___81_2364.FStar_Tactics_Types.opts);
                   FStar_Tactics_Types.is_guard =
                     (uu___81_2364.FStar_Tactics_Types.is_guard)
                 })))
  
let (norm_term_env :
  env ->
    FStar_Syntax_Embeddings.norm_step Prims.list ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac)
  =
  fun e  ->
    fun s  ->
      fun t  ->
        let uu____2382 =
          mlog
            (fun uu____2387  ->
               let uu____2388 = FStar_Syntax_Print.term_to_string t  in
               FStar_Util.print1 "norm_term: tm = %s\n" uu____2388)
            (fun uu____2390  ->
               bind get
                 (fun ps  ->
                    mlog
                      (fun uu____2395  ->
                         let uu____2396 =
                           tts ps.FStar_Tactics_Types.main_context t  in
                         FStar_Util.print1 "norm_term_env: t = %s\n"
                           uu____2396)
                      (fun uu____2399  ->
                         let uu____2400 = __tc e t  in
                         bind uu____2400
                           (fun uu____2422  ->
                              match uu____2422 with
                              | (t1,uu____2432,guard) ->
                                  (FStar_TypeChecker_Rel.force_trivial_guard
                                     e guard;
                                   (let steps =
                                      let uu____2438 =
                                        FStar_TypeChecker_Normalize.tr_norm_steps
                                          s
                                         in
                                      FStar_List.append
                                        [FStar_TypeChecker_Normalize.Reify;
                                        FStar_TypeChecker_Normalize.UnfoldTac]
                                        uu____2438
                                       in
                                    let t2 =
                                      normalize steps
                                        ps.FStar_Tactics_Types.main_context
                                        t1
                                       in
                                    ret t2))))))
           in
        FStar_All.pipe_left (wrap_err "norm_term") uu____2382
  
let (refine_intro : Prims.unit tac) =
  let uu____2450 =
    bind cur_goal
      (fun g  ->
         let uu____2457 =
           FStar_TypeChecker_Rel.base_and_refinement
             g.FStar_Tactics_Types.context g.FStar_Tactics_Types.goal_ty
            in
         match uu____2457 with
         | (uu____2470,FStar_Pervasives_Native.None ) ->
             fail "not a refinement"
         | (t,FStar_Pervasives_Native.Some (bv,phi)) ->
             let g1 =
               let uu___82_2495 = g  in
               {
                 FStar_Tactics_Types.context =
                   (uu___82_2495.FStar_Tactics_Types.context);
                 FStar_Tactics_Types.witness =
                   (uu___82_2495.FStar_Tactics_Types.witness);
                 FStar_Tactics_Types.goal_ty = t;
                 FStar_Tactics_Types.opts =
                   (uu___82_2495.FStar_Tactics_Types.opts);
                 FStar_Tactics_Types.is_guard =
                   (uu___82_2495.FStar_Tactics_Types.is_guard)
               }  in
             let uu____2496 =
               let uu____2501 =
                 let uu____2506 =
                   let uu____2507 = FStar_Syntax_Syntax.mk_binder bv  in
                   [uu____2507]  in
                 FStar_Syntax_Subst.open_term uu____2506 phi  in
               match uu____2501 with
               | (bvs,phi1) ->
                   let uu____2514 =
                     let uu____2515 = FStar_List.hd bvs  in
                     FStar_Pervasives_Native.fst uu____2515  in
                   (uu____2514, phi1)
                in
             (match uu____2496 with
              | (bv1,phi1) ->
                  let uu____2528 =
                    let uu____2531 =
                      FStar_Syntax_Subst.subst
                        [FStar_Syntax_Syntax.NT
                           (bv1, (g.FStar_Tactics_Types.witness))] phi1
                       in
                    mk_irrelevant_goal "refine_intro refinement"
                      g.FStar_Tactics_Types.context uu____2531
                      g.FStar_Tactics_Types.opts
                     in
                  bind uu____2528
                    (fun g2  ->
                       bind dismiss (fun uu____2535  -> add_goals [g1; g2]))))
     in
  FStar_All.pipe_left (wrap_err "refine_intro") uu____2450 
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
             let uu____2559 = __tc env t  in
             bind uu____2559
               (fun uu____2579  ->
                  match uu____2579 with
                  | (t1,typ,guard) ->
                      let uu____2591 =
                        if force_guard
                        then
                          must_trivial "__exact"
                            goal.FStar_Tactics_Types.context guard
                        else
                          add_goal_from_guard "__exact typing"
                            goal.FStar_Tactics_Types.context guard
                            goal.FStar_Tactics_Types.opts
                         in
                      bind uu____2591
                        (fun uu____2598  ->
                           mlog
                             (fun uu____2602  ->
                                let uu____2603 =
                                  tts goal.FStar_Tactics_Types.context typ
                                   in
                                let uu____2604 =
                                  tts goal.FStar_Tactics_Types.context
                                    goal.FStar_Tactics_Types.goal_ty
                                   in
                                FStar_Util.print2
                                  "exact: unifying %s and %s\n" uu____2603
                                  uu____2604)
                             (fun uu____2607  ->
                                let uu____2608 =
                                  do_unify goal.FStar_Tactics_Types.context
                                    typ goal.FStar_Tactics_Types.goal_ty
                                   in
                                bind uu____2608
                                  (fun b  ->
                                     if b
                                     then solve goal t1
                                     else
                                       (let uu____2616 =
                                          tts
                                            goal.FStar_Tactics_Types.context
                                            t1
                                           in
                                        let uu____2617 =
                                          tts
                                            goal.FStar_Tactics_Types.context
                                            typ
                                           in
                                        let uu____2618 =
                                          tts
                                            goal.FStar_Tactics_Types.context
                                            goal.FStar_Tactics_Types.goal_ty
                                           in
                                        let uu____2619 =
                                          tts
                                            goal.FStar_Tactics_Types.context
                                            goal.FStar_Tactics_Types.witness
                                           in
                                        fail4
                                          "%s : %s does not exactly solve the goal %s (witness = %s)"
                                          uu____2616 uu____2617 uu____2618
                                          uu____2619))))))
  
let (t_exact :
  Prims.bool -> Prims.bool -> FStar_Syntax_Syntax.term -> Prims.unit tac) =
  fun set_expected_typ1  ->
    fun force_guard  ->
      fun tm  ->
        let uu____2633 =
          mlog
            (fun uu____2638  ->
               let uu____2639 = FStar_Syntax_Print.term_to_string tm  in
               FStar_Util.print1 "t_exact: tm = %s\n" uu____2639)
            (fun uu____2642  ->
               let uu____2643 =
                 let uu____2650 =
                   __exact_now set_expected_typ1 force_guard tm  in
                 trytac' uu____2650  in
               bind uu____2643
                 (fun uu___56_2659  ->
                    match uu___56_2659 with
                    | FStar_Util.Inr r -> ret ()
                    | FStar_Util.Inl e ->
                        let uu____2668 =
                          let uu____2675 =
                            let uu____2678 =
                              norm [FStar_Syntax_Embeddings.Delta]  in
                            bind uu____2678
                              (fun uu____2682  ->
                                 bind refine_intro
                                   (fun uu____2684  ->
                                      __exact_now set_expected_typ1
                                        force_guard tm))
                             in
                          trytac' uu____2675  in
                        bind uu____2668
                          (fun uu___55_2691  ->
                             match uu___55_2691 with
                             | FStar_Util.Inr r -> ret ()
                             | FStar_Util.Inl uu____2699 -> fail e)))
           in
        FStar_All.pipe_left (wrap_err "exact") uu____2633
  
let (uvar_free_in_goal :
  FStar_Syntax_Syntax.uvar -> FStar_Tactics_Types.goal -> Prims.bool) =
  fun u  ->
    fun g  ->
      if g.FStar_Tactics_Types.is_guard
      then false
      else
        (let free_uvars =
           let uu____2714 =
             let uu____2721 =
               FStar_Syntax_Free.uvars g.FStar_Tactics_Types.goal_ty  in
             FStar_Util.set_elements uu____2721  in
           FStar_List.map FStar_Pervasives_Native.fst uu____2714  in
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
          let uu____2781 = f x  in
          bind uu____2781
            (fun y  ->
               let uu____2789 = mapM f xs  in
               bind uu____2789 (fun ys  -> ret (y :: ys)))
  
exception NoUnif 
let (uu___is_NoUnif : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with | NoUnif  -> true | uu____2807 -> false
  
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
               (fun uu____2825  ->
                  let uu____2826 = FStar_Syntax_Print.term_to_string tm  in
                  FStar_Util.print1 ">>> Calling __exact(%s)\n" uu____2826)
               (fun uu____2829  ->
                  let uu____2830 =
                    let uu____2835 = t_exact false true tm  in
                    trytac uu____2835  in
                  bind uu____2830
                    (fun uu___57_2842  ->
                       match uu___57_2842 with
                       | FStar_Pervasives_Native.Some r -> ret ()
                       | FStar_Pervasives_Native.None  ->
                           mlog
                             (fun uu____2850  ->
                                let uu____2851 =
                                  FStar_Syntax_Print.term_to_string typ  in
                                FStar_Util.print1 ">>> typ = %s\n" uu____2851)
                             (fun uu____2854  ->
                                let uu____2855 =
                                  FStar_Syntax_Util.arrow_one typ  in
                                match uu____2855 with
                                | FStar_Pervasives_Native.None  ->
                                    FStar_Exn.raise NoUnif
                                | FStar_Pervasives_Native.Some ((bv,aq),c) ->
                                    mlog
                                      (fun uu____2887  ->
                                         let uu____2888 =
                                           FStar_Syntax_Print.binder_to_string
                                             (bv, aq)
                                            in
                                         FStar_Util.print1
                                           "__apply: pushing binder %s\n"
                                           uu____2888)
                                      (fun uu____2891  ->
                                         let uu____2892 =
                                           let uu____2893 =
                                             FStar_Syntax_Util.is_total_comp
                                               c
                                              in
                                           Prims.op_Negation uu____2893  in
                                         if uu____2892
                                         then
                                           fail "apply: not total codomain"
                                         else
                                           (let uu____2897 =
                                              new_uvar "apply"
                                                goal.FStar_Tactics_Types.context
                                                bv.FStar_Syntax_Syntax.sort
                                               in
                                            bind uu____2897
                                              (fun u  ->
                                                 let tm' =
                                                   FStar_Syntax_Syntax.mk_Tm_app
                                                     tm [(u, aq)]
                                                     FStar_Pervasives_Native.None
                                                     tm.FStar_Syntax_Syntax.pos
                                                    in
                                                 let typ' =
                                                   let uu____2917 =
                                                     comp_to_typ c  in
                                                   FStar_All.pipe_left
                                                     (FStar_Syntax_Subst.subst
                                                        [FStar_Syntax_Syntax.NT
                                                           (bv, u)])
                                                     uu____2917
                                                    in
                                                 let uu____2918 =
                                                   __apply uopt tm' typ'  in
                                                 bind uu____2918
                                                   (fun uu____2926  ->
                                                      let u1 =
                                                        bnorm
                                                          goal.FStar_Tactics_Types.context
                                                          u
                                                         in
                                                      let uu____2928 =
                                                        let uu____2929 =
                                                          let uu____2932 =
                                                            let uu____2933 =
                                                              FStar_Syntax_Util.head_and_args
                                                                u1
                                                               in
                                                            FStar_Pervasives_Native.fst
                                                              uu____2933
                                                             in
                                                          FStar_Syntax_Subst.compress
                                                            uu____2932
                                                           in
                                                        uu____2929.FStar_Syntax_Syntax.n
                                                         in
                                                      match uu____2928 with
                                                      | FStar_Syntax_Syntax.Tm_uvar
                                                          (uvar,uu____2961)
                                                          ->
                                                          bind get
                                                            (fun ps  ->
                                                               let uu____2989
                                                                 =
                                                                 uopt &&
                                                                   (uvar_free
                                                                    uvar ps)
                                                                  in
                                                               if uu____2989
                                                               then ret ()
                                                               else
                                                                 (let uu____2993
                                                                    =
                                                                    let uu____2996
                                                                    =
                                                                    let uu___83_2997
                                                                    = goal
                                                                     in
                                                                    let uu____2998
                                                                    =
                                                                    bnorm
                                                                    goal.FStar_Tactics_Types.context
                                                                    u1  in
                                                                    let uu____2999
                                                                    =
                                                                    bnorm
                                                                    goal.FStar_Tactics_Types.context
                                                                    bv.FStar_Syntax_Syntax.sort
                                                                     in
                                                                    {
                                                                    FStar_Tactics_Types.context
                                                                    =
                                                                    (uu___83_2997.FStar_Tactics_Types.context);
                                                                    FStar_Tactics_Types.witness
                                                                    =
                                                                    uu____2998;
                                                                    FStar_Tactics_Types.goal_ty
                                                                    =
                                                                    uu____2999;
                                                                    FStar_Tactics_Types.opts
                                                                    =
                                                                    (uu___83_2997.FStar_Tactics_Types.opts);
                                                                    FStar_Tactics_Types.is_guard
                                                                    = false
                                                                    }  in
                                                                    [uu____2996]
                                                                     in
                                                                  add_goals
                                                                    uu____2993))
                                                      | t -> ret ()))))))))
  
let try_unif : 'a . 'a tac -> 'a tac -> 'a tac =
  fun t  ->
    fun t'  -> mk_tac (fun ps  -> try run t ps with | NoUnif  -> run t' ps)
  
let (apply : Prims.bool -> FStar_Syntax_Syntax.term -> Prims.unit tac) =
  fun uopt  ->
    fun tm  ->
      let uu____3045 =
        mlog
          (fun uu____3050  ->
             let uu____3051 = FStar_Syntax_Print.term_to_string tm  in
             FStar_Util.print1 "apply: tm = %s\n" uu____3051)
          (fun uu____3053  ->
             bind cur_goal
               (fun goal  ->
                  let uu____3057 = __tc goal.FStar_Tactics_Types.context tm
                     in
                  bind uu____3057
                    (fun uu____3079  ->
                       match uu____3079 with
                       | (tm1,typ,guard) ->
                           let typ1 =
                             bnorm goal.FStar_Tactics_Types.context typ  in
                           let uu____3092 =
                             let uu____3095 =
                               let uu____3098 = __apply uopt tm1 typ1  in
                               bind uu____3098
                                 (fun uu____3102  ->
                                    add_goal_from_guard "apply guard"
                                      goal.FStar_Tactics_Types.context guard
                                      goal.FStar_Tactics_Types.opts)
                                in
                             focus uu____3095  in
                           let uu____3103 =
                             let uu____3106 =
                               tts goal.FStar_Tactics_Types.context tm1  in
                             let uu____3107 =
                               tts goal.FStar_Tactics_Types.context typ1  in
                             let uu____3108 =
                               tts goal.FStar_Tactics_Types.context
                                 goal.FStar_Tactics_Types.goal_ty
                                in
                             fail3
                               "Cannot instantiate %s (of type %s) to match goal (%s)"
                               uu____3106 uu____3107 uu____3108
                              in
                           try_unif uu____3092 uu____3103)))
         in
      FStar_All.pipe_left (wrap_err "apply") uu____3045
  
let (apply_lemma : FStar_Syntax_Syntax.term -> Prims.unit tac) =
  fun tm  ->
    let uu____3120 =
      let uu____3123 =
        mlog
          (fun uu____3128  ->
             let uu____3129 = FStar_Syntax_Print.term_to_string tm  in
             FStar_Util.print1 "apply_lemma: tm = %s\n" uu____3129)
          (fun uu____3132  ->
             let is_unit_t t =
               let uu____3137 =
                 let uu____3138 = FStar_Syntax_Subst.compress t  in
                 uu____3138.FStar_Syntax_Syntax.n  in
               match uu____3137 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.unit_lid
                   -> true
               | uu____3142 -> false  in
             bind cur_goal
               (fun goal  ->
                  let uu____3146 = __tc goal.FStar_Tactics_Types.context tm
                     in
                  bind uu____3146
                    (fun uu____3168  ->
                       match uu____3168 with
                       | (tm1,t,guard) ->
                           let uu____3180 =
                             FStar_Syntax_Util.arrow_formals_comp t  in
                           (match uu____3180 with
                            | (bs,comp) ->
                                if
                                  Prims.op_Negation
                                    (FStar_Syntax_Util.is_lemma_comp comp)
                                then fail "not a lemma"
                                else
                                  (let uu____3210 =
                                     FStar_List.fold_left
                                       (fun uu____3256  ->
                                          fun uu____3257  ->
                                            match (uu____3256, uu____3257)
                                            with
                                            | ((uvs,guard1,subst1),(b,aq)) ->
                                                let b_t =
                                                  FStar_Syntax_Subst.subst
                                                    subst1
                                                    b.FStar_Syntax_Syntax.sort
                                                   in
                                                let uu____3360 =
                                                  is_unit_t b_t  in
                                                if uu____3360
                                                then
                                                  (((FStar_Syntax_Util.exp_unit,
                                                      aq) :: uvs), guard1,
                                                    ((FStar_Syntax_Syntax.NT
                                                        (b,
                                                          FStar_Syntax_Util.exp_unit))
                                                    :: subst1))
                                                else
                                                  (let uu____3398 =
                                                     FStar_TypeChecker_Util.new_implicit_var
                                                       "apply_lemma"
                                                       (goal.FStar_Tactics_Types.goal_ty).FStar_Syntax_Syntax.pos
                                                       goal.FStar_Tactics_Types.context
                                                       b_t
                                                      in
                                                   match uu____3398 with
                                                   | (u,uu____3428,g_u) ->
                                                       let uu____3442 =
                                                         FStar_TypeChecker_Rel.conj_guard
                                                           guard1 g_u
                                                          in
                                                       (((u, aq) :: uvs),
                                                         uu____3442,
                                                         ((FStar_Syntax_Syntax.NT
                                                             (b, u)) ::
                                                         subst1))))
                                       ([], guard, []) bs
                                      in
                                   match uu____3210 with
                                   | (uvs,implicits,subst1) ->
                                       let uvs1 = FStar_List.rev uvs  in
                                       let comp1 =
                                         FStar_Syntax_Subst.subst_comp subst1
                                           comp
                                          in
                                       let uu____3512 =
                                         let uu____3521 =
                                           let uu____3530 =
                                             FStar_Syntax_Util.comp_to_comp_typ
                                               comp1
                                              in
                                           uu____3530.FStar_Syntax_Syntax.effect_args
                                            in
                                         match uu____3521 with
                                         | pre::post::uu____3541 ->
                                             ((FStar_Pervasives_Native.fst
                                                 pre),
                                               (FStar_Pervasives_Native.fst
                                                  post))
                                         | uu____3582 ->
                                             failwith
                                               "apply_lemma: impossible: not a lemma"
                                          in
                                       (match uu____3512 with
                                        | (pre,post) ->
                                            let post1 =
                                              let uu____3614 =
                                                let uu____3623 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    FStar_Syntax_Util.exp_unit
                                                   in
                                                [uu____3623]  in
                                              FStar_Syntax_Util.mk_app post
                                                uu____3614
                                               in
                                            let uu____3624 =
                                              let uu____3627 =
                                                FStar_Syntax_Util.mk_squash
                                                  FStar_Syntax_Syntax.U_zero
                                                  post1
                                                 in
                                              do_unify
                                                goal.FStar_Tactics_Types.context
                                                uu____3627
                                                goal.FStar_Tactics_Types.goal_ty
                                               in
                                            bind uu____3624
                                              (fun b  ->
                                                 if Prims.op_Negation b
                                                 then
                                                   let uu____3635 =
                                                     tts
                                                       goal.FStar_Tactics_Types.context
                                                       tm1
                                                      in
                                                   let uu____3636 =
                                                     let uu____3637 =
                                                       FStar_Syntax_Util.mk_squash
                                                         FStar_Syntax_Syntax.U_zero
                                                         post1
                                                        in
                                                     tts
                                                       goal.FStar_Tactics_Types.context
                                                       uu____3637
                                                      in
                                                   let uu____3638 =
                                                     tts
                                                       goal.FStar_Tactics_Types.context
                                                       goal.FStar_Tactics_Types.goal_ty
                                                      in
                                                   fail3
                                                     "Cannot instantiate lemma %s (with postcondition: %s) to match goal (%s)"
                                                     uu____3635 uu____3636
                                                     uu____3638
                                                 else
                                                   (let uu____3640 =
                                                      add_implicits
                                                        implicits.FStar_TypeChecker_Env.implicits
                                                       in
                                                    bind uu____3640
                                                      (fun uu____3645  ->
                                                         let uu____3646 =
                                                           solve goal
                                                             FStar_Syntax_Util.exp_unit
                                                            in
                                                         bind uu____3646
                                                           (fun uu____3654 
                                                              ->
                                                              let is_free_uvar
                                                                uv t1 =
                                                                let free_uvars
                                                                  =
                                                                  let uu____3665
                                                                    =
                                                                    let uu____3672
                                                                    =
                                                                    FStar_Syntax_Free.uvars
                                                                    t1  in
                                                                    FStar_Util.set_elements
                                                                    uu____3672
                                                                     in
                                                                  FStar_List.map
                                                                    FStar_Pervasives_Native.fst
                                                                    uu____3665
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
                                                                let uu____3713
                                                                  =
                                                                  FStar_Syntax_Util.head_and_args
                                                                    t1
                                                                   in
                                                                match uu____3713
                                                                with
                                                                | (hd1,uu____3729)
                                                                    ->
                                                                    (
                                                                    match 
                                                                    hd1.FStar_Syntax_Syntax.n
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Tm_uvar
                                                                    (uv,uu____3751)
                                                                    ->
                                                                    appears
                                                                    uv goals
                                                                    | 
                                                                    uu____3776
                                                                    -> false)
                                                                 in
                                                              let uu____3777
                                                                =
                                                                FStar_All.pipe_right
                                                                  implicits.FStar_TypeChecker_Env.implicits
                                                                  (mapM
                                                                    (fun
                                                                    uu____3849
                                                                     ->
                                                                    match uu____3849
                                                                    with
                                                                    | 
                                                                    (_msg,env,_uvar,term,typ,uu____3877)
                                                                    ->
                                                                    let uu____3878
                                                                    =
                                                                    FStar_Syntax_Util.head_and_args
                                                                    term  in
                                                                    (match uu____3878
                                                                    with
                                                                    | 
                                                                    (hd1,uu____3904)
                                                                    ->
                                                                    let uu____3925
                                                                    =
                                                                    let uu____3926
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    hd1  in
                                                                    uu____3926.FStar_Syntax_Syntax.n
                                                                     in
                                                                    (match uu____3925
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Tm_uvar
                                                                    uu____3939
                                                                    ->
                                                                    let uu____3956
                                                                    =
                                                                    let uu____3965
                                                                    =
                                                                    let uu____3968
                                                                    =
                                                                    let uu___86_3969
                                                                    = goal
                                                                     in
                                                                    let uu____3970
                                                                    =
                                                                    bnorm
                                                                    goal.FStar_Tactics_Types.context
                                                                    term  in
                                                                    let uu____3971
                                                                    =
                                                                    bnorm
                                                                    goal.FStar_Tactics_Types.context
                                                                    typ  in
                                                                    {
                                                                    FStar_Tactics_Types.context
                                                                    =
                                                                    (uu___86_3969.FStar_Tactics_Types.context);
                                                                    FStar_Tactics_Types.witness
                                                                    =
                                                                    uu____3970;
                                                                    FStar_Tactics_Types.goal_ty
                                                                    =
                                                                    uu____3971;
                                                                    FStar_Tactics_Types.opts
                                                                    =
                                                                    (uu___86_3969.FStar_Tactics_Types.opts);
                                                                    FStar_Tactics_Types.is_guard
                                                                    =
                                                                    (uu___86_3969.FStar_Tactics_Types.is_guard)
                                                                    }  in
                                                                    [uu____3968]
                                                                     in
                                                                    (uu____3965,
                                                                    [])  in
                                                                    ret
                                                                    uu____3956
                                                                    | 
                                                                    uu____3984
                                                                    ->
                                                                    let g_typ
                                                                    =
                                                                    let uu____3986
                                                                    =
                                                                    FStar_Options.__temp_fast_implicits
                                                                    ()  in
                                                                    if
                                                                    uu____3986
                                                                    then
                                                                    FStar_TypeChecker_TcTerm.check_type_of_well_typed_term
                                                                    false env
                                                                    term typ
                                                                    else
                                                                    (let term1
                                                                    =
                                                                    bnorm env
                                                                    term  in
                                                                    let uu____3989
                                                                    =
                                                                    let uu____3996
                                                                    =
                                                                    FStar_TypeChecker_Env.set_expected_typ
                                                                    env typ
                                                                     in
                                                                    env.FStar_TypeChecker_Env.type_of
                                                                    uu____3996
                                                                    term1  in
                                                                    match uu____3989
                                                                    with
                                                                    | 
                                                                    (uu____3997,uu____3998,g_typ)
                                                                    -> g_typ)
                                                                     in
                                                                    let uu____4000
                                                                    =
                                                                    goal_from_guard
                                                                    "apply_lemma solved arg"
                                                                    goal.FStar_Tactics_Types.context
                                                                    g_typ
                                                                    goal.FStar_Tactics_Types.opts
                                                                     in
                                                                    bind
                                                                    uu____4000
                                                                    (fun
                                                                    uu___58_4016
                                                                     ->
                                                                    match uu___58_4016
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
                                                              bind uu____3777
                                                                (fun goals_ 
                                                                   ->
                                                                   let sub_goals
                                                                    =
                                                                    let uu____4084
                                                                    =
                                                                    FStar_List.map
                                                                    FStar_Pervasives_Native.fst
                                                                    goals_
                                                                     in
                                                                    FStar_List.flatten
                                                                    uu____4084
                                                                     in
                                                                   let smt_goals
                                                                    =
                                                                    let uu____4106
                                                                    =
                                                                    FStar_List.map
                                                                    FStar_Pervasives_Native.snd
                                                                    goals_
                                                                     in
                                                                    FStar_List.flatten
                                                                    uu____4106
                                                                     in
                                                                   let rec filter'
                                                                    a f xs =
                                                                    match xs
                                                                    with
                                                                    | 
                                                                    [] -> []
                                                                    | 
                                                                    x::xs1 ->
                                                                    let uu____4161
                                                                    = f x xs1
                                                                     in
                                                                    if
                                                                    uu____4161
                                                                    then
                                                                    let uu____4164
                                                                    =
                                                                    filter'
                                                                    () f xs1
                                                                     in x ::
                                                                    uu____4164
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
                                                                    let uu____4178
                                                                    =
                                                                    checkone
                                                                    g.FStar_Tactics_Types.witness
                                                                    goals  in
                                                                    Prims.op_Negation
                                                                    uu____4178))
                                                                    a438 a439)
                                                                    (Obj.magic
                                                                    sub_goals))
                                                                     in
                                                                   let uu____4179
                                                                    =
                                                                    add_goal_from_guard
                                                                    "apply_lemma guard"
                                                                    goal.FStar_Tactics_Types.context
                                                                    guard
                                                                    goal.FStar_Tactics_Types.opts
                                                                     in
                                                                   bind
                                                                    uu____4179
                                                                    (fun
                                                                    uu____4184
                                                                     ->
                                                                    let uu____4185
                                                                    =
                                                                    let uu____4188
                                                                    =
                                                                    let uu____4189
                                                                    =
                                                                    let uu____4190
                                                                    =
                                                                    FStar_Syntax_Util.mk_squash
                                                                    FStar_Syntax_Syntax.U_zero
                                                                    pre  in
                                                                    istrivial
                                                                    goal.FStar_Tactics_Types.context
                                                                    uu____4190
                                                                     in
                                                                    Prims.op_Negation
                                                                    uu____4189
                                                                     in
                                                                    if
                                                                    uu____4188
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
                                                                    uu____4185
                                                                    (fun
                                                                    uu____4196
                                                                     ->
                                                                    let uu____4197
                                                                    =
                                                                    add_smt_goals
                                                                    smt_goals
                                                                     in
                                                                    bind
                                                                    uu____4197
                                                                    (fun
                                                                    uu____4201
                                                                     ->
                                                                    add_goals
                                                                    sub_goals1))))))))))))))
         in
      focus uu____3123  in
    FStar_All.pipe_left (wrap_err "apply_lemma") uu____3120
  
let (destruct_eq' :
  FStar_Syntax_Syntax.typ ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun typ  ->
    let uu____4221 = FStar_Syntax_Util.destruct_typ_as_formula typ  in
    match uu____4221 with
    | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn
        (l,uu____4231::(e1,uu____4233)::(e2,uu____4235)::[])) when
        FStar_Ident.lid_equals l FStar_Parser_Const.eq2_lid ->
        FStar_Pervasives_Native.Some (e1, e2)
    | uu____4294 -> FStar_Pervasives_Native.None
  
let (destruct_eq :
  FStar_Syntax_Syntax.typ ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun typ  ->
    let uu____4316 = destruct_eq' typ  in
    match uu____4316 with
    | FStar_Pervasives_Native.Some t -> FStar_Pervasives_Native.Some t
    | FStar_Pervasives_Native.None  ->
        let uu____4346 = FStar_Syntax_Util.un_squash typ  in
        (match uu____4346 with
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
        let uu____4402 = FStar_TypeChecker_Env.pop_bv e1  in
        match uu____4402 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (bv',e') ->
            if FStar_Syntax_Syntax.bv_eq bvar bv'
            then FStar_Pervasives_Native.Some (e', [])
            else
              (let uu____4450 = aux e'  in
               FStar_Util.map_opt uu____4450
                 (fun uu____4474  ->
                    match uu____4474 with | (e'',bvs) -> (e'', (bv' :: bvs))))
         in
      let uu____4495 = aux e  in
      FStar_Util.map_opt uu____4495
        (fun uu____4519  ->
           match uu____4519 with | (e',bvs) -> (e', (FStar_List.rev bvs)))
  
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
          let uu____4574 = split_env b1 g.FStar_Tactics_Types.context  in
          FStar_Util.map_opt uu____4574
            (fun uu____4598  ->
               match uu____4598 with
               | (e0,bvs) ->
                   let s1 bv =
                     let uu___87_4615 = bv  in
                     let uu____4616 =
                       FStar_Syntax_Subst.subst s bv.FStar_Syntax_Syntax.sort
                        in
                     {
                       FStar_Syntax_Syntax.ppname =
                         (uu___87_4615.FStar_Syntax_Syntax.ppname);
                       FStar_Syntax_Syntax.index =
                         (uu___87_4615.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort = uu____4616
                     }  in
                   let bvs1 = FStar_List.map s1 bvs  in
                   let c = push_bvs e0 (b2 :: bvs1)  in
                   let w =
                     FStar_Syntax_Subst.subst s g.FStar_Tactics_Types.witness
                      in
                   let t =
                     FStar_Syntax_Subst.subst s g.FStar_Tactics_Types.goal_ty
                      in
                   let uu___88_4625 = g  in
                   {
                     FStar_Tactics_Types.context = c;
                     FStar_Tactics_Types.witness = w;
                     FStar_Tactics_Types.goal_ty = t;
                     FStar_Tactics_Types.opts =
                       (uu___88_4625.FStar_Tactics_Types.opts);
                     FStar_Tactics_Types.is_guard =
                       (uu___88_4625.FStar_Tactics_Types.is_guard)
                   })
  
let (rewrite : FStar_Syntax_Syntax.binder -> Prims.unit tac) =
  fun h  ->
    bind cur_goal
      (fun goal  ->
         let uu____4638 = h  in
         match uu____4638 with
         | (bv,uu____4642) ->
             mlog
               (fun uu____4646  ->
                  let uu____4647 = FStar_Syntax_Print.bv_to_string bv  in
                  let uu____4648 =
                    tts goal.FStar_Tactics_Types.context
                      bv.FStar_Syntax_Syntax.sort
                     in
                  FStar_Util.print2 "+++Rewrite %s : %s\n" uu____4647
                    uu____4648)
               (fun uu____4651  ->
                  let uu____4652 =
                    split_env bv goal.FStar_Tactics_Types.context  in
                  match uu____4652 with
                  | FStar_Pervasives_Native.None  ->
                      fail "rewrite: binder not found in environment"
                  | FStar_Pervasives_Native.Some (e0,bvs) ->
                      let uu____4681 =
                        destruct_eq bv.FStar_Syntax_Syntax.sort  in
                      (match uu____4681 with
                       | FStar_Pervasives_Native.Some (x,e) ->
                           let uu____4696 =
                             let uu____4697 = FStar_Syntax_Subst.compress x
                                in
                             uu____4697.FStar_Syntax_Syntax.n  in
                           (match uu____4696 with
                            | FStar_Syntax_Syntax.Tm_name x1 ->
                                let s = [FStar_Syntax_Syntax.NT (x1, e)]  in
                                let s1 bv1 =
                                  let uu___89_4710 = bv1  in
                                  let uu____4711 =
                                    FStar_Syntax_Subst.subst s
                                      bv1.FStar_Syntax_Syntax.sort
                                     in
                                  {
                                    FStar_Syntax_Syntax.ppname =
                                      (uu___89_4710.FStar_Syntax_Syntax.ppname);
                                    FStar_Syntax_Syntax.index =
                                      (uu___89_4710.FStar_Syntax_Syntax.index);
                                    FStar_Syntax_Syntax.sort = uu____4711
                                  }  in
                                let bvs1 = FStar_List.map s1 bvs  in
                                let uu____4717 =
                                  let uu___90_4718 = goal  in
                                  let uu____4719 = push_bvs e0 (bv :: bvs1)
                                     in
                                  let uu____4720 =
                                    FStar_Syntax_Subst.subst s
                                      goal.FStar_Tactics_Types.witness
                                     in
                                  let uu____4721 =
                                    FStar_Syntax_Subst.subst s
                                      goal.FStar_Tactics_Types.goal_ty
                                     in
                                  {
                                    FStar_Tactics_Types.context = uu____4719;
                                    FStar_Tactics_Types.witness = uu____4720;
                                    FStar_Tactics_Types.goal_ty = uu____4721;
                                    FStar_Tactics_Types.opts =
                                      (uu___90_4718.FStar_Tactics_Types.opts);
                                    FStar_Tactics_Types.is_guard =
                                      (uu___90_4718.FStar_Tactics_Types.is_guard)
                                  }  in
                                replace_cur uu____4717
                            | uu____4722 ->
                                fail
                                  "rewrite: Not an equality hypothesis with a variable on the LHS")
                       | uu____4723 ->
                           fail "rewrite: Not an equality hypothesis")))
  
let (rename_to :
  FStar_Syntax_Syntax.binder -> Prims.string -> Prims.unit tac) =
  fun b  ->
    fun s  ->
      bind cur_goal
        (fun goal  ->
           let uu____4748 = b  in
           match uu____4748 with
           | (bv,uu____4752) ->
               let bv' =
                 FStar_Syntax_Syntax.freshen_bv
                   (let uu___91_4756 = bv  in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (FStar_Ident.mk_ident
                           (s,
                             ((bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange)));
                      FStar_Syntax_Syntax.index =
                        (uu___91_4756.FStar_Syntax_Syntax.index);
                      FStar_Syntax_Syntax.sort =
                        (uu___91_4756.FStar_Syntax_Syntax.sort)
                    })
                  in
               let s1 =
                 let uu____4760 =
                   let uu____4761 =
                     let uu____4768 = FStar_Syntax_Syntax.bv_to_name bv'  in
                     (bv, uu____4768)  in
                   FStar_Syntax_Syntax.NT uu____4761  in
                 [uu____4760]  in
               let uu____4769 = subst_goal bv bv' s1 goal  in
               (match uu____4769 with
                | FStar_Pervasives_Native.None  ->
                    fail "rename_to: binder not found in environment"
                | FStar_Pervasives_Native.Some goal1 -> replace_cur goal1))
  
let (binder_retype : FStar_Syntax_Syntax.binder -> Prims.unit tac) =
  fun b  ->
    bind cur_goal
      (fun goal  ->
         let uu____4788 = b  in
         match uu____4788 with
         | (bv,uu____4792) ->
             let uu____4793 = split_env bv goal.FStar_Tactics_Types.context
                in
             (match uu____4793 with
              | FStar_Pervasives_Native.None  ->
                  fail "binder_retype: binder is not present in environment"
              | FStar_Pervasives_Native.Some (e0,bvs) ->
                  let uu____4822 = FStar_Syntax_Util.type_u ()  in
                  (match uu____4822 with
                   | (ty,u) ->
                       let uu____4831 = new_uvar "binder_retype" e0 ty  in
                       bind uu____4831
                         (fun t'  ->
                            let bv'' =
                              let uu___92_4841 = bv  in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___92_4841.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___92_4841.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = t'
                              }  in
                            let s =
                              let uu____4845 =
                                let uu____4846 =
                                  let uu____4853 =
                                    FStar_Syntax_Syntax.bv_to_name bv''  in
                                  (bv, uu____4853)  in
                                FStar_Syntax_Syntax.NT uu____4846  in
                              [uu____4845]  in
                            let bvs1 =
                              FStar_List.map
                                (fun b1  ->
                                   let uu___93_4861 = b1  in
                                   let uu____4862 =
                                     FStar_Syntax_Subst.subst s
                                       b1.FStar_Syntax_Syntax.sort
                                      in
                                   {
                                     FStar_Syntax_Syntax.ppname =
                                       (uu___93_4861.FStar_Syntax_Syntax.ppname);
                                     FStar_Syntax_Syntax.index =
                                       (uu___93_4861.FStar_Syntax_Syntax.index);
                                     FStar_Syntax_Syntax.sort = uu____4862
                                   }) bvs
                               in
                            let env' = push_bvs e0 (bv'' :: bvs1)  in
                            bind dismiss
                              (fun uu____4868  ->
                                 let uu____4869 =
                                   let uu____4872 =
                                     let uu____4875 =
                                       let uu___94_4876 = goal  in
                                       let uu____4877 =
                                         FStar_Syntax_Subst.subst s
                                           goal.FStar_Tactics_Types.witness
                                          in
                                       let uu____4878 =
                                         FStar_Syntax_Subst.subst s
                                           goal.FStar_Tactics_Types.goal_ty
                                          in
                                       {
                                         FStar_Tactics_Types.context = env';
                                         FStar_Tactics_Types.witness =
                                           uu____4877;
                                         FStar_Tactics_Types.goal_ty =
                                           uu____4878;
                                         FStar_Tactics_Types.opts =
                                           (uu___94_4876.FStar_Tactics_Types.opts);
                                         FStar_Tactics_Types.is_guard =
                                           (uu___94_4876.FStar_Tactics_Types.is_guard)
                                       }  in
                                     [uu____4875]  in
                                   add_goals uu____4872  in
                                 bind uu____4869
                                   (fun uu____4881  ->
                                      let uu____4882 =
                                        FStar_Syntax_Util.mk_eq2
                                          (FStar_Syntax_Syntax.U_succ u) ty
                                          bv.FStar_Syntax_Syntax.sort t'
                                         in
                                      add_irrelevant_goal
                                        "binder_retype equation" e0
                                        uu____4882
                                        goal.FStar_Tactics_Types.opts))))))
  
let (norm_binder_type :
  FStar_Syntax_Embeddings.norm_step Prims.list ->
    FStar_Syntax_Syntax.binder -> Prims.unit tac)
  =
  fun s  ->
    fun b  ->
      bind cur_goal
        (fun goal  ->
           let uu____4903 = b  in
           match uu____4903 with
           | (bv,uu____4907) ->
               let uu____4908 = split_env bv goal.FStar_Tactics_Types.context
                  in
               (match uu____4908 with
                | FStar_Pervasives_Native.None  ->
                    fail
                      "binder_retype: binder is not present in environment"
                | FStar_Pervasives_Native.Some (e0,bvs) ->
                    let steps =
                      let uu____4940 =
                        FStar_TypeChecker_Normalize.tr_norm_steps s  in
                      FStar_List.append
                        [FStar_TypeChecker_Normalize.Reify;
                        FStar_TypeChecker_Normalize.UnfoldTac] uu____4940
                       in
                    let sort' =
                      normalize steps e0 bv.FStar_Syntax_Syntax.sort  in
                    let bv' =
                      let uu___95_4945 = bv  in
                      {
                        FStar_Syntax_Syntax.ppname =
                          (uu___95_4945.FStar_Syntax_Syntax.ppname);
                        FStar_Syntax_Syntax.index =
                          (uu___95_4945.FStar_Syntax_Syntax.index);
                        FStar_Syntax_Syntax.sort = sort'
                      }  in
                    let env' = push_bvs e0 (bv' :: bvs)  in
                    replace_cur
                      (let uu___96_4949 = goal  in
                       {
                         FStar_Tactics_Types.context = env';
                         FStar_Tactics_Types.witness =
                           (uu___96_4949.FStar_Tactics_Types.witness);
                         FStar_Tactics_Types.goal_ty =
                           (uu___96_4949.FStar_Tactics_Types.goal_ty);
                         FStar_Tactics_Types.opts =
                           (uu___96_4949.FStar_Tactics_Types.opts);
                         FStar_Tactics_Types.is_guard =
                           (uu___96_4949.FStar_Tactics_Types.is_guard)
                       })))
  
let (revert : Prims.unit tac) =
  bind cur_goal
    (fun goal  ->
       let uu____4957 =
         FStar_TypeChecker_Env.pop_bv goal.FStar_Tactics_Types.context  in
       match uu____4957 with
       | FStar_Pervasives_Native.None  -> fail "Cannot revert; empty context"
       | FStar_Pervasives_Native.Some (x,env') ->
           let typ' =
             let uu____4979 =
               FStar_Syntax_Syntax.mk_Total goal.FStar_Tactics_Types.goal_ty
                in
             FStar_Syntax_Util.arrow [(x, FStar_Pervasives_Native.None)]
               uu____4979
              in
           let w' =
             FStar_Syntax_Util.abs [(x, FStar_Pervasives_Native.None)]
               goal.FStar_Tactics_Types.witness FStar_Pervasives_Native.None
              in
           replace_cur
             (let uu___97_5013 = goal  in
              {
                FStar_Tactics_Types.context = env';
                FStar_Tactics_Types.witness = w';
                FStar_Tactics_Types.goal_ty = typ';
                FStar_Tactics_Types.opts =
                  (uu___97_5013.FStar_Tactics_Types.opts);
                FStar_Tactics_Types.is_guard =
                  (uu___97_5013.FStar_Tactics_Types.is_guard)
              }))
  
let (free_in :
  FStar_Syntax_Syntax.bv -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun bv  ->
    fun t  ->
      let uu____5020 = FStar_Syntax_Free.names t  in
      FStar_Util.set_mem bv uu____5020
  
let rec (clear : FStar_Syntax_Syntax.binder -> Prims.unit tac) =
  fun b  ->
    let bv = FStar_Pervasives_Native.fst b  in
    bind cur_goal
      (fun goal  ->
         mlog
           (fun uu____5036  ->
              let uu____5037 = FStar_Syntax_Print.binder_to_string b  in
              let uu____5038 =
                let uu____5039 =
                  let uu____5040 =
                    FStar_TypeChecker_Env.all_binders
                      goal.FStar_Tactics_Types.context
                     in
                  FStar_All.pipe_right uu____5040 FStar_List.length  in
                FStar_All.pipe_right uu____5039 FStar_Util.string_of_int  in
              FStar_Util.print2 "Clear of (%s), env has %s binders\n"
                uu____5037 uu____5038)
           (fun uu____5051  ->
              let uu____5052 = split_env bv goal.FStar_Tactics_Types.context
                 in
              match uu____5052 with
              | FStar_Pervasives_Native.None  ->
                  fail "Cannot clear; binder not in environment"
              | FStar_Pervasives_Native.Some (e',bvs) ->
                  let rec check bvs1 =
                    match bvs1 with
                    | [] -> ret ()
                    | bv'::bvs2 ->
                        let uu____5097 =
                          free_in bv bv'.FStar_Syntax_Syntax.sort  in
                        if uu____5097
                        then
                          let uu____5100 =
                            let uu____5101 =
                              FStar_Syntax_Print.bv_to_string bv'  in
                            FStar_Util.format1
                              "Cannot clear; binder present in the type of %s"
                              uu____5101
                             in
                          fail uu____5100
                        else check bvs2
                     in
                  let uu____5103 =
                    free_in bv goal.FStar_Tactics_Types.goal_ty  in
                  if uu____5103
                  then fail "Cannot clear; binder present in goal"
                  else
                    (let uu____5107 = check bvs  in
                     bind uu____5107
                       (fun uu____5113  ->
                          let env' = push_bvs e' bvs  in
                          let uu____5115 =
                            new_uvar "clear.witness" env'
                              goal.FStar_Tactics_Types.goal_ty
                             in
                          bind uu____5115
                            (fun ut  ->
                               let uu____5121 =
                                 do_unify goal.FStar_Tactics_Types.context
                                   goal.FStar_Tactics_Types.witness ut
                                  in
                               bind uu____5121
                                 (fun b1  ->
                                    if b1
                                    then
                                      replace_cur
                                        (let uu___98_5130 = goal  in
                                         {
                                           FStar_Tactics_Types.context = env';
                                           FStar_Tactics_Types.witness = ut;
                                           FStar_Tactics_Types.goal_ty =
                                             (uu___98_5130.FStar_Tactics_Types.goal_ty);
                                           FStar_Tactics_Types.opts =
                                             (uu___98_5130.FStar_Tactics_Types.opts);
                                           FStar_Tactics_Types.is_guard =
                                             (uu___98_5130.FStar_Tactics_Types.is_guard)
                                         })
                                    else
                                      fail
                                        "Cannot clear; binder appears in witness"))))))
  
let (clear_top : Prims.unit tac) =
  bind cur_goal
    (fun goal  ->
       let uu____5139 =
         FStar_TypeChecker_Env.pop_bv goal.FStar_Tactics_Types.context  in
       match uu____5139 with
       | FStar_Pervasives_Native.None  -> fail "Cannot clear; empty context"
       | FStar_Pervasives_Native.Some (x,uu____5153) ->
           let uu____5158 = FStar_Syntax_Syntax.mk_binder x  in
           clear uu____5158)
  
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
           let uu___99_5174 = g  in
           {
             FStar_Tactics_Types.context = ctx';
             FStar_Tactics_Types.witness =
               (uu___99_5174.FStar_Tactics_Types.witness);
             FStar_Tactics_Types.goal_ty =
               (uu___99_5174.FStar_Tactics_Types.goal_ty);
             FStar_Tactics_Types.opts =
               (uu___99_5174.FStar_Tactics_Types.opts);
             FStar_Tactics_Types.is_guard =
               (uu___99_5174.FStar_Tactics_Types.is_guard)
           }  in
         bind dismiss (fun uu____5176  -> add_goals [g']))
  
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
           let uu___100_5192 = g  in
           {
             FStar_Tactics_Types.context = ctx';
             FStar_Tactics_Types.witness =
               (uu___100_5192.FStar_Tactics_Types.witness);
             FStar_Tactics_Types.goal_ty =
               (uu___100_5192.FStar_Tactics_Types.goal_ty);
             FStar_Tactics_Types.opts =
               (uu___100_5192.FStar_Tactics_Types.opts);
             FStar_Tactics_Types.is_guard =
               (uu___100_5192.FStar_Tactics_Types.is_guard)
           }  in
         bind dismiss (fun uu____5194  -> add_goals [g']))
  
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
            let uu____5226 = FStar_Syntax_Subst.compress t  in
            uu____5226.FStar_Syntax_Syntax.n  in
          let uu____5229 =
            if d = FStar_Tactics_Types.TopDown
            then
              f env
                (let uu___102_5235 = t  in
                 {
                   FStar_Syntax_Syntax.n = tn;
                   FStar_Syntax_Syntax.pos =
                     (uu___102_5235.FStar_Syntax_Syntax.pos);
                   FStar_Syntax_Syntax.vars =
                     (uu___102_5235.FStar_Syntax_Syntax.vars)
                 })
            else ret t  in
          bind uu____5229
            (fun t1  ->
               let tn1 =
                 let uu____5243 =
                   let uu____5244 = FStar_Syntax_Subst.compress t1  in
                   uu____5244.FStar_Syntax_Syntax.n  in
                 match uu____5243 with
                 | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
                     let ff = tac_fold_env d f env  in
                     let uu____5276 = ff hd1  in
                     bind uu____5276
                       (fun hd2  ->
                          let fa uu____5296 =
                            match uu____5296 with
                            | (a,q) ->
                                let uu____5309 = ff a  in
                                bind uu____5309 (fun a1  -> ret (a1, q))
                             in
                          let uu____5322 = mapM fa args  in
                          bind uu____5322
                            (fun args1  ->
                               ret (FStar_Syntax_Syntax.Tm_app (hd2, args1))))
                 | FStar_Syntax_Syntax.Tm_abs (bs,t2,k) ->
                     let uu____5382 = FStar_Syntax_Subst.open_term bs t2  in
                     (match uu____5382 with
                      | (bs1,t') ->
                          let uu____5391 =
                            let uu____5394 =
                              FStar_TypeChecker_Env.push_binders env bs1  in
                            tac_fold_env d f uu____5394 t'  in
                          bind uu____5391
                            (fun t''  ->
                               let uu____5398 =
                                 let uu____5399 =
                                   let uu____5416 =
                                     FStar_Syntax_Subst.close_binders bs1  in
                                   let uu____5417 =
                                     FStar_Syntax_Subst.close bs1 t''  in
                                   (uu____5416, uu____5417, k)  in
                                 FStar_Syntax_Syntax.Tm_abs uu____5399  in
                               ret uu____5398))
                 | FStar_Syntax_Syntax.Tm_arrow (bs,k) -> ret tn
                 | uu____5438 -> ret tn  in
               bind tn1
                 (fun tn2  ->
                    let t' =
                      let uu___101_5445 = t1  in
                      {
                        FStar_Syntax_Syntax.n = tn2;
                        FStar_Syntax_Syntax.pos =
                          (uu___101_5445.FStar_Syntax_Syntax.pos);
                        FStar_Syntax_Syntax.vars =
                          (uu___101_5445.FStar_Syntax_Syntax.vars)
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
            let uu____5474 = FStar_TypeChecker_TcTerm.tc_term env t  in
            match uu____5474 with
            | (t1,lcomp,g) ->
                let uu____5486 =
                  (let uu____5489 =
                     FStar_Syntax_Util.is_pure_or_ghost_lcomp lcomp  in
                   Prims.op_Negation uu____5489) ||
                    (let uu____5491 = FStar_TypeChecker_Rel.is_trivial g  in
                     Prims.op_Negation uu____5491)
                   in
                if uu____5486
                then ret t1
                else
                  (let rewrite_eq =
                     let typ = lcomp.FStar_Syntax_Syntax.res_typ  in
                     let uu____5501 = new_uvar "pointwise_rec" env typ  in
                     bind uu____5501
                       (fun ut  ->
                          log ps
                            (fun uu____5512  ->
                               let uu____5513 =
                                 FStar_Syntax_Print.term_to_string t1  in
                               let uu____5514 =
                                 FStar_Syntax_Print.term_to_string ut  in
                               FStar_Util.print2
                                 "Pointwise_rec: making equality\n\t%s ==\n\t%s\n"
                                 uu____5513 uu____5514);
                          (let uu____5515 =
                             let uu____5518 =
                               let uu____5519 =
                                 FStar_TypeChecker_TcTerm.universe_of env typ
                                  in
                               FStar_Syntax_Util.mk_eq2 uu____5519 typ t1 ut
                                in
                             add_irrelevant_goal "pointwise_rec equation" env
                               uu____5518 opts
                              in
                           bind uu____5515
                             (fun uu____5522  ->
                                let uu____5523 =
                                  bind tau
                                    (fun uu____5529  ->
                                       let ut1 =
                                         FStar_TypeChecker_Normalize.reduce_uvar_solutions
                                           env ut
                                          in
                                       log ps
                                         (fun uu____5535  ->
                                            let uu____5536 =
                                              FStar_Syntax_Print.term_to_string
                                                t1
                                               in
                                            let uu____5537 =
                                              FStar_Syntax_Print.term_to_string
                                                ut1
                                               in
                                            FStar_Util.print2
                                              "Pointwise_rec: succeeded rewriting\n\t%s to\n\t%s\n"
                                              uu____5536 uu____5537);
                                       ret ut1)
                                   in
                                focus uu____5523)))
                      in
                   let uu____5538 = trytac' rewrite_eq  in
                   bind uu____5538
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
          let uu____5686 = FStar_Syntax_Subst.compress t  in
          maybe_continue ctrl uu____5686
            (fun t1  ->
               let uu____5690 =
                 f env
                   (let uu___105_5699 = t1  in
                    {
                      FStar_Syntax_Syntax.n = (t1.FStar_Syntax_Syntax.n);
                      FStar_Syntax_Syntax.pos =
                        (uu___105_5699.FStar_Syntax_Syntax.pos);
                      FStar_Syntax_Syntax.vars =
                        (uu___105_5699.FStar_Syntax_Syntax.vars)
                    })
                  in
               bind uu____5690
                 (fun uu____5711  ->
                    match uu____5711 with
                    | (t2,ctrl1) ->
                        maybe_continue ctrl1 t2
                          (fun t3  ->
                             let uu____5730 =
                               let uu____5731 =
                                 FStar_Syntax_Subst.compress t3  in
                               uu____5731.FStar_Syntax_Syntax.n  in
                             match uu____5730 with
                             | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
                                 let uu____5764 =
                                   ctrl_tac_fold f env ctrl1 hd1  in
                                 bind uu____5764
                                   (fun uu____5789  ->
                                      match uu____5789 with
                                      | (hd2,ctrl2) ->
                                          let ctrl3 = keep_going ctrl2  in
                                          let uu____5805 =
                                            ctrl_tac_fold_args f env ctrl3
                                              args
                                             in
                                          bind uu____5805
                                            (fun uu____5832  ->
                                               match uu____5832 with
                                               | (args1,ctrl4) ->
                                                   ret
                                                     ((let uu___103_5862 = t3
                                                          in
                                                       {
                                                         FStar_Syntax_Syntax.n
                                                           =
                                                           (FStar_Syntax_Syntax.Tm_app
                                                              (hd2, args1));
                                                         FStar_Syntax_Syntax.pos
                                                           =
                                                           (uu___103_5862.FStar_Syntax_Syntax.pos);
                                                         FStar_Syntax_Syntax.vars
                                                           =
                                                           (uu___103_5862.FStar_Syntax_Syntax.vars)
                                                       }), ctrl4)))
                             | FStar_Syntax_Syntax.Tm_abs (bs,t4,k) ->
                                 let uu____5888 =
                                   FStar_Syntax_Subst.open_term bs t4  in
                                 (match uu____5888 with
                                  | (bs1,t') ->
                                      let uu____5903 =
                                        let uu____5910 =
                                          FStar_TypeChecker_Env.push_binders
                                            env bs1
                                           in
                                        ctrl_tac_fold f uu____5910 ctrl1 t'
                                         in
                                      bind uu____5903
                                        (fun uu____5928  ->
                                           match uu____5928 with
                                           | (t'',ctrl2) ->
                                               let uu____5943 =
                                                 let uu____5950 =
                                                   let uu___104_5953 = t4  in
                                                   let uu____5956 =
                                                     let uu____5957 =
                                                       let uu____5974 =
                                                         FStar_Syntax_Subst.close_binders
                                                           bs1
                                                          in
                                                       let uu____5975 =
                                                         FStar_Syntax_Subst.close
                                                           bs1 t''
                                                          in
                                                       (uu____5974,
                                                         uu____5975, k)
                                                        in
                                                     FStar_Syntax_Syntax.Tm_abs
                                                       uu____5957
                                                      in
                                                   {
                                                     FStar_Syntax_Syntax.n =
                                                       uu____5956;
                                                     FStar_Syntax_Syntax.pos
                                                       =
                                                       (uu___104_5953.FStar_Syntax_Syntax.pos);
                                                     FStar_Syntax_Syntax.vars
                                                       =
                                                       (uu___104_5953.FStar_Syntax_Syntax.vars)
                                                   }  in
                                                 (uu____5950, ctrl2)  in
                                               ret uu____5943))
                             | FStar_Syntax_Syntax.Tm_arrow (bs,k) ->
                                 ret (t3, ctrl1)
                             | uu____6008 -> ret (t3, ctrl1))))

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
              let uu____6059 = ctrl_tac_fold f env ctrl t  in
              bind uu____6059
                (fun uu____6087  ->
                   match uu____6087 with
                   | (t1,ctrl1) ->
                       let uu____6106 = ctrl_tac_fold_args f env ctrl1 ts1
                          in
                       bind uu____6106
                         (fun uu____6137  ->
                            match uu____6137 with
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
              let uu____6221 =
                let uu____6228 =
                  add_irrelevant_goal "dummy" env FStar_Syntax_Util.t_true
                    opts
                   in
                bind uu____6228
                  (fun uu____6237  ->
                     let uu____6238 = ctrl t1  in
                     bind uu____6238
                       (fun res  -> bind trivial (fun uu____6265  -> ret res)))
                 in
              bind uu____6221
                (fun uu____6281  ->
                   match uu____6281 with
                   | (should_rewrite,ctrl1) ->
                       if Prims.op_Negation should_rewrite
                       then ret (t1, ctrl1)
                       else
                         (let uu____6305 =
                            FStar_TypeChecker_TcTerm.tc_term env t1  in
                          match uu____6305 with
                          | (t2,lcomp,g) ->
                              let uu____6321 =
                                (let uu____6324 =
                                   FStar_Syntax_Util.is_pure_or_ghost_lcomp
                                     lcomp
                                    in
                                 Prims.op_Negation uu____6324) ||
                                  (let uu____6326 =
                                     FStar_TypeChecker_Rel.is_trivial g  in
                                   Prims.op_Negation uu____6326)
                                 in
                              if uu____6321
                              then ret (t2, globalStop)
                              else
                                (let typ = lcomp.FStar_Syntax_Syntax.res_typ
                                    in
                                 let uu____6341 =
                                   new_uvar "pointwise_rec" env typ  in
                                 bind uu____6341
                                   (fun ut  ->
                                      log ps
                                        (fun uu____6356  ->
                                           let uu____6357 =
                                             FStar_Syntax_Print.term_to_string
                                               t2
                                              in
                                           let uu____6358 =
                                             FStar_Syntax_Print.term_to_string
                                               ut
                                              in
                                           FStar_Util.print2
                                             "Pointwise_rec: making equality\n\t%s ==\n\t%s\n"
                                             uu____6357 uu____6358);
                                      (let uu____6359 =
                                         let uu____6362 =
                                           let uu____6363 =
                                             FStar_TypeChecker_TcTerm.universe_of
                                               env typ
                                              in
                                           FStar_Syntax_Util.mk_eq2
                                             uu____6363 typ t2 ut
                                            in
                                         add_irrelevant_goal
                                           "rewrite_rec equation" env
                                           uu____6362 opts
                                          in
                                       bind uu____6359
                                         (fun uu____6370  ->
                                            let uu____6371 =
                                              bind rewriter
                                                (fun uu____6385  ->
                                                   let ut1 =
                                                     FStar_TypeChecker_Normalize.reduce_uvar_solutions
                                                       env ut
                                                      in
                                                   log ps
                                                     (fun uu____6391  ->
                                                        let uu____6392 =
                                                          FStar_Syntax_Print.term_to_string
                                                            t2
                                                           in
                                                        let uu____6393 =
                                                          FStar_Syntax_Print.term_to_string
                                                            ut1
                                                           in
                                                        FStar_Util.print2
                                                          "rewrite_rec: succeeded rewriting\n\t%s to\n\t%s\n"
                                                          uu____6392
                                                          uu____6393);
                                                   ret (ut1, ctrl1))
                                               in
                                            focus uu____6371))))))
  
let (topdown_rewrite :
  (FStar_Syntax_Syntax.term ->
     (Prims.bool,FStar_BigInt.t) FStar_Pervasives_Native.tuple2 tac)
    -> Prims.unit tac -> Prims.unit tac)
  =
  fun ctrl  ->
    fun rewriter  ->
      bind get
        (fun ps  ->
           let uu____6437 =
             match ps.FStar_Tactics_Types.goals with
             | g::gs -> (g, gs)
             | [] -> failwith "Pointwise: no goals"  in
           match uu____6437 with
           | (g,gs) ->
               let gt1 = g.FStar_Tactics_Types.goal_ty  in
               (log ps
                  (fun uu____6474  ->
                     let uu____6475 = FStar_Syntax_Print.term_to_string gt1
                        in
                     FStar_Util.print1 "Pointwise starting with %s\n"
                       uu____6475);
                bind dismiss_all
                  (fun uu____6478  ->
                     let uu____6479 =
                       ctrl_tac_fold
                         (rewrite_rec ps ctrl rewriter
                            g.FStar_Tactics_Types.opts)
                         g.FStar_Tactics_Types.context keepGoing gt1
                        in
                     bind uu____6479
                       (fun uu____6497  ->
                          match uu____6497 with
                          | (gt',uu____6505) ->
                              (log ps
                                 (fun uu____6509  ->
                                    let uu____6510 =
                                      FStar_Syntax_Print.term_to_string gt'
                                       in
                                    FStar_Util.print1
                                      "Pointwise seems to have succeded with %s\n"
                                      uu____6510);
                               (let uu____6511 = push_goals gs  in
                                bind uu____6511
                                  (fun uu____6515  ->
                                     add_goals
                                       [(let uu___106_6517 = g  in
                                         {
                                           FStar_Tactics_Types.context =
                                             (uu___106_6517.FStar_Tactics_Types.context);
                                           FStar_Tactics_Types.witness =
                                             (uu___106_6517.FStar_Tactics_Types.witness);
                                           FStar_Tactics_Types.goal_ty = gt';
                                           FStar_Tactics_Types.opts =
                                             (uu___106_6517.FStar_Tactics_Types.opts);
                                           FStar_Tactics_Types.is_guard =
                                             (uu___106_6517.FStar_Tactics_Types.is_guard)
                                         })])))))))
  
let (pointwise :
  FStar_Tactics_Types.direction -> Prims.unit tac -> Prims.unit tac) =
  fun d  ->
    fun tau  ->
      bind get
        (fun ps  ->
           let uu____6539 =
             match ps.FStar_Tactics_Types.goals with
             | g::gs -> (g, gs)
             | [] -> failwith "Pointwise: no goals"  in
           match uu____6539 with
           | (g,gs) ->
               let gt1 = g.FStar_Tactics_Types.goal_ty  in
               (log ps
                  (fun uu____6576  ->
                     let uu____6577 = FStar_Syntax_Print.term_to_string gt1
                        in
                     FStar_Util.print1 "Pointwise starting with %s\n"
                       uu____6577);
                bind dismiss_all
                  (fun uu____6580  ->
                     let uu____6581 =
                       tac_fold_env d
                         (pointwise_rec ps tau g.FStar_Tactics_Types.opts)
                         g.FStar_Tactics_Types.context gt1
                        in
                     bind uu____6581
                       (fun gt'  ->
                          log ps
                            (fun uu____6591  ->
                               let uu____6592 =
                                 FStar_Syntax_Print.term_to_string gt'  in
                               FStar_Util.print1
                                 "Pointwise seems to have succeded with %s\n"
                                 uu____6592);
                          (let uu____6593 = push_goals gs  in
                           bind uu____6593
                             (fun uu____6597  ->
                                add_goals
                                  [(let uu___107_6599 = g  in
                                    {
                                      FStar_Tactics_Types.context =
                                        (uu___107_6599.FStar_Tactics_Types.context);
                                      FStar_Tactics_Types.witness =
                                        (uu___107_6599.FStar_Tactics_Types.witness);
                                      FStar_Tactics_Types.goal_ty = gt';
                                      FStar_Tactics_Types.opts =
                                        (uu___107_6599.FStar_Tactics_Types.opts);
                                      FStar_Tactics_Types.is_guard =
                                        (uu___107_6599.FStar_Tactics_Types.is_guard)
                                    })]))))))
  
let (trefl : Prims.unit tac) =
  bind cur_goal
    (fun g  ->
       let uu____6619 =
         FStar_Syntax_Util.un_squash g.FStar_Tactics_Types.goal_ty  in
       match uu____6619 with
       | FStar_Pervasives_Native.Some t ->
           let uu____6631 = FStar_Syntax_Util.head_and_args' t  in
           (match uu____6631 with
            | (hd1,args) ->
                let uu____6664 =
                  let uu____6677 =
                    let uu____6678 = FStar_Syntax_Util.un_uinst hd1  in
                    uu____6678.FStar_Syntax_Syntax.n  in
                  (uu____6677, args)  in
                (match uu____6664 with
                 | (FStar_Syntax_Syntax.Tm_fvar
                    fv,uu____6692::(l,uu____6694)::(r,uu____6696)::[]) when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.eq2_lid
                     ->
                     let uu____6743 =
                       do_unify g.FStar_Tactics_Types.context l r  in
                     bind uu____6743
                       (fun b  ->
                          if Prims.op_Negation b
                          then
                            let uu____6752 =
                              tts g.FStar_Tactics_Types.context l  in
                            let uu____6753 =
                              tts g.FStar_Tactics_Types.context r  in
                            fail2 "trefl: not a trivial equality (%s vs %s)"
                              uu____6752 uu____6753
                          else solve g FStar_Syntax_Util.exp_unit)
                 | (hd2,uu____6756) ->
                     let uu____6773 = tts g.FStar_Tactics_Types.context t  in
                     fail1 "trefl: not an equality (%s)" uu____6773))
       | FStar_Pervasives_Native.None  -> fail "not an irrelevant goal")
  
let (dup : Prims.unit tac) =
  bind cur_goal
    (fun g  ->
       let uu____6783 =
         new_uvar "dup" g.FStar_Tactics_Types.context
           g.FStar_Tactics_Types.goal_ty
          in
       bind uu____6783
         (fun u  ->
            let g' =
              let uu___108_6790 = g  in
              {
                FStar_Tactics_Types.context =
                  (uu___108_6790.FStar_Tactics_Types.context);
                FStar_Tactics_Types.witness = u;
                FStar_Tactics_Types.goal_ty =
                  (uu___108_6790.FStar_Tactics_Types.goal_ty);
                FStar_Tactics_Types.opts =
                  (uu___108_6790.FStar_Tactics_Types.opts);
                FStar_Tactics_Types.is_guard =
                  (uu___108_6790.FStar_Tactics_Types.is_guard)
              }  in
            bind dismiss
              (fun uu____6793  ->
                 let uu____6794 =
                   let uu____6797 =
                     let uu____6798 =
                       FStar_TypeChecker_TcTerm.universe_of
                         g.FStar_Tactics_Types.context
                         g.FStar_Tactics_Types.goal_ty
                        in
                     FStar_Syntax_Util.mk_eq2 uu____6798
                       g.FStar_Tactics_Types.goal_ty u
                       g.FStar_Tactics_Types.witness
                      in
                   add_irrelevant_goal "dup equation"
                     g.FStar_Tactics_Types.context uu____6797
                     g.FStar_Tactics_Types.opts
                    in
                 bind uu____6794
                   (fun uu____6801  ->
                      let uu____6802 = add_goals [g']  in
                      bind uu____6802 (fun uu____6806  -> ret ())))))
  
let (flip : Prims.unit tac) =
  bind get
    (fun ps  ->
       match ps.FStar_Tactics_Types.goals with
       | g1::g2::gs ->
           set
             (let uu___109_6825 = ps  in
              {
                FStar_Tactics_Types.main_context =
                  (uu___109_6825.FStar_Tactics_Types.main_context);
                FStar_Tactics_Types.main_goal =
                  (uu___109_6825.FStar_Tactics_Types.main_goal);
                FStar_Tactics_Types.all_implicits =
                  (uu___109_6825.FStar_Tactics_Types.all_implicits);
                FStar_Tactics_Types.goals = (g2 :: g1 :: gs);
                FStar_Tactics_Types.smt_goals =
                  (uu___109_6825.FStar_Tactics_Types.smt_goals);
                FStar_Tactics_Types.depth =
                  (uu___109_6825.FStar_Tactics_Types.depth);
                FStar_Tactics_Types.__dump =
                  (uu___109_6825.FStar_Tactics_Types.__dump);
                FStar_Tactics_Types.psc =
                  (uu___109_6825.FStar_Tactics_Types.psc);
                FStar_Tactics_Types.entry_range =
                  (uu___109_6825.FStar_Tactics_Types.entry_range)
              })
       | uu____6826 -> fail "flip: less than 2 goals")
  
let (later : Prims.unit tac) =
  bind get
    (fun ps  ->
       match ps.FStar_Tactics_Types.goals with
       | [] -> ret ()
       | g::gs ->
           set
             (let uu___110_6843 = ps  in
              {
                FStar_Tactics_Types.main_context =
                  (uu___110_6843.FStar_Tactics_Types.main_context);
                FStar_Tactics_Types.main_goal =
                  (uu___110_6843.FStar_Tactics_Types.main_goal);
                FStar_Tactics_Types.all_implicits =
                  (uu___110_6843.FStar_Tactics_Types.all_implicits);
                FStar_Tactics_Types.goals = (FStar_List.append gs [g]);
                FStar_Tactics_Types.smt_goals =
                  (uu___110_6843.FStar_Tactics_Types.smt_goals);
                FStar_Tactics_Types.depth =
                  (uu___110_6843.FStar_Tactics_Types.depth);
                FStar_Tactics_Types.__dump =
                  (uu___110_6843.FStar_Tactics_Types.__dump);
                FStar_Tactics_Types.psc =
                  (uu___110_6843.FStar_Tactics_Types.psc);
                FStar_Tactics_Types.entry_range =
                  (uu___110_6843.FStar_Tactics_Types.entry_range)
              }))
  
let (qed : Prims.unit tac) =
  bind get
    (fun ps  ->
       match ps.FStar_Tactics_Types.goals with
       | [] -> ret ()
       | uu____6852 -> fail "Not done!")
  
let (cases :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 tac)
  =
  fun t  ->
    let uu____6870 =
      bind cur_goal
        (fun g  ->
           let uu____6884 = __tc g.FStar_Tactics_Types.context t  in
           bind uu____6884
             (fun uu____6920  ->
                match uu____6920 with
                | (t1,typ,guard) ->
                    let uu____6936 = FStar_Syntax_Util.head_and_args typ  in
                    (match uu____6936 with
                     | (hd1,args) ->
                         let uu____6979 =
                           let uu____6992 =
                             let uu____6993 = FStar_Syntax_Util.un_uinst hd1
                                in
                             uu____6993.FStar_Syntax_Syntax.n  in
                           (uu____6992, args)  in
                         (match uu____6979 with
                          | (FStar_Syntax_Syntax.Tm_fvar
                             fv,(p,uu____7012)::(q,uu____7014)::[]) when
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
                                let uu___111_7052 = g  in
                                let uu____7053 =
                                  FStar_TypeChecker_Env.push_bv
                                    g.FStar_Tactics_Types.context v_p
                                   in
                                {
                                  FStar_Tactics_Types.context = uu____7053;
                                  FStar_Tactics_Types.witness =
                                    (uu___111_7052.FStar_Tactics_Types.witness);
                                  FStar_Tactics_Types.goal_ty =
                                    (uu___111_7052.FStar_Tactics_Types.goal_ty);
                                  FStar_Tactics_Types.opts =
                                    (uu___111_7052.FStar_Tactics_Types.opts);
                                  FStar_Tactics_Types.is_guard =
                                    (uu___111_7052.FStar_Tactics_Types.is_guard)
                                }  in
                              let g2 =
                                let uu___112_7055 = g  in
                                let uu____7056 =
                                  FStar_TypeChecker_Env.push_bv
                                    g.FStar_Tactics_Types.context v_q
                                   in
                                {
                                  FStar_Tactics_Types.context = uu____7056;
                                  FStar_Tactics_Types.witness =
                                    (uu___112_7055.FStar_Tactics_Types.witness);
                                  FStar_Tactics_Types.goal_ty =
                                    (uu___112_7055.FStar_Tactics_Types.goal_ty);
                                  FStar_Tactics_Types.opts =
                                    (uu___112_7055.FStar_Tactics_Types.opts);
                                  FStar_Tactics_Types.is_guard =
                                    (uu___112_7055.FStar_Tactics_Types.is_guard)
                                }  in
                              bind dismiss
                                (fun uu____7063  ->
                                   let uu____7064 = add_goals [g1; g2]  in
                                   bind uu____7064
                                     (fun uu____7073  ->
                                        let uu____7074 =
                                          let uu____7079 =
                                            FStar_Syntax_Syntax.bv_to_name
                                              v_p
                                             in
                                          let uu____7080 =
                                            FStar_Syntax_Syntax.bv_to_name
                                              v_q
                                             in
                                          (uu____7079, uu____7080)  in
                                        ret uu____7074))
                          | uu____7085 ->
                              let uu____7098 =
                                tts g.FStar_Tactics_Types.context typ  in
                              fail1 "Not a disjunction: %s" uu____7098))))
       in
    FStar_All.pipe_left (wrap_err "cases") uu____6870
  
let (set_options : Prims.string -> Prims.unit tac) =
  fun s  ->
    bind cur_goal
      (fun g  ->
         FStar_Options.push ();
         (let uu____7136 = FStar_Util.smap_copy g.FStar_Tactics_Types.opts
             in
          FStar_Options.set uu____7136);
         (let res = FStar_Options.set_options FStar_Options.Set s  in
          let opts' = FStar_Options.peek ()  in
          FStar_Options.pop ();
          (match res with
           | FStar_Getopt.Success  ->
               let g' =
                 let uu___113_7143 = g  in
                 {
                   FStar_Tactics_Types.context =
                     (uu___113_7143.FStar_Tactics_Types.context);
                   FStar_Tactics_Types.witness =
                     (uu___113_7143.FStar_Tactics_Types.witness);
                   FStar_Tactics_Types.goal_ty =
                     (uu___113_7143.FStar_Tactics_Types.goal_ty);
                   FStar_Tactics_Types.opts = opts';
                   FStar_Tactics_Types.is_guard =
                     (uu___113_7143.FStar_Tactics_Types.is_guard)
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
      let uu____7187 =
        bind cur_goal
          (fun goal  ->
             let env =
               FStar_TypeChecker_Env.set_expected_typ
                 goal.FStar_Tactics_Types.context ty
                in
             let uu____7195 = __tc env tm  in
             bind uu____7195
               (fun uu____7215  ->
                  match uu____7215 with
                  | (tm1,typ,guard) ->
                      (FStar_TypeChecker_Rel.force_trivial_guard env guard;
                       ret tm1)))
         in
      FStar_All.pipe_left (wrap_err "unquote") uu____7187
  
let (uvar_env :
  env ->
    FStar_Syntax_Syntax.typ FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.term tac)
  =
  fun env  ->
    fun ty  ->
      let uu____7246 =
        match ty with
        | FStar_Pervasives_Native.Some ty1 -> ret ty1
        | FStar_Pervasives_Native.None  ->
            let uu____7252 =
              let uu____7253 = FStar_Syntax_Util.type_u ()  in
              FStar_All.pipe_left FStar_Pervasives_Native.fst uu____7253  in
            new_uvar "uvar_env.2" env uu____7252
         in
      bind uu____7246
        (fun typ  ->
           let uu____7265 = new_uvar "uvar_env" env typ  in
           bind uu____7265 (fun t  -> ret t))
  
let (unshelve : FStar_Syntax_Syntax.term -> Prims.unit tac) =
  fun t  ->
    let uu____7277 =
      bind cur_goal
        (fun goal  ->
           let uu____7283 = __tc goal.FStar_Tactics_Types.context t  in
           bind uu____7283
             (fun uu____7303  ->
                match uu____7303 with
                | (t1,typ,guard) ->
                    let uu____7315 =
                      must_trivial "unshelve"
                        goal.FStar_Tactics_Types.context guard
                       in
                    bind uu____7315
                      (fun uu____7320  ->
                         let uu____7321 =
                           let uu____7324 =
                             let uu___114_7325 = goal  in
                             let uu____7326 =
                               bnorm goal.FStar_Tactics_Types.context t1  in
                             let uu____7327 =
                               bnorm goal.FStar_Tactics_Types.context typ  in
                             {
                               FStar_Tactics_Types.context =
                                 (uu___114_7325.FStar_Tactics_Types.context);
                               FStar_Tactics_Types.witness = uu____7326;
                               FStar_Tactics_Types.goal_ty = uu____7327;
                               FStar_Tactics_Types.opts =
                                 (uu___114_7325.FStar_Tactics_Types.opts);
                               FStar_Tactics_Types.is_guard = false
                             }  in
                           [uu____7324]  in
                         add_goals uu____7321)))
       in
    FStar_All.pipe_left (wrap_err "unshelve") uu____7277
  
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
          (fun uu____7360  ->
             let uu____7361 = FStar_Options.unsafe_tactic_exec ()  in
             if uu____7361
             then
               let s =
                 FStar_Util.launch_process true "tactic_launch" prog args
                   input (fun uu____7367  -> fun uu____7368  -> false)
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
        (fun uu____7382  ->
           let uu____7383 =
             FStar_Syntax_Syntax.gen_bv nm FStar_Pervasives_Native.None t  in
           ret uu____7383)
  
let (change : FStar_Syntax_Syntax.typ -> Prims.unit tac) =
  fun ty  ->
    let uu____7391 =
      mlog
        (fun uu____7396  ->
           let uu____7397 = FStar_Syntax_Print.term_to_string ty  in
           FStar_Util.print1 "change: ty = %s\n" uu____7397)
        (fun uu____7399  ->
           bind cur_goal
             (fun g  ->
                let uu____7403 = __tc g.FStar_Tactics_Types.context ty  in
                bind uu____7403
                  (fun uu____7423  ->
                     match uu____7423 with
                     | (ty1,uu____7433,guard) ->
                         let uu____7435 =
                           must_trivial "change"
                             g.FStar_Tactics_Types.context guard
                            in
                         bind uu____7435
                           (fun uu____7440  ->
                              let uu____7441 =
                                do_unify g.FStar_Tactics_Types.context
                                  g.FStar_Tactics_Types.goal_ty ty1
                                 in
                              bind uu____7441
                                (fun bb  ->
                                   if bb
                                   then
                                     replace_cur
                                       (let uu___115_7450 = g  in
                                        {
                                          FStar_Tactics_Types.context =
                                            (uu___115_7450.FStar_Tactics_Types.context);
                                          FStar_Tactics_Types.witness =
                                            (uu___115_7450.FStar_Tactics_Types.witness);
                                          FStar_Tactics_Types.goal_ty = ty1;
                                          FStar_Tactics_Types.opts =
                                            (uu___115_7450.FStar_Tactics_Types.opts);
                                          FStar_Tactics_Types.is_guard =
                                            (uu___115_7450.FStar_Tactics_Types.is_guard)
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
                                      let uu____7457 =
                                        do_unify
                                          g.FStar_Tactics_Types.context ng
                                          nty
                                         in
                                      bind uu____7457
                                        (fun b  ->
                                           if b
                                           then
                                             replace_cur
                                               (let uu___116_7466 = g  in
                                                {
                                                  FStar_Tactics_Types.context
                                                    =
                                                    (uu___116_7466.FStar_Tactics_Types.context);
                                                  FStar_Tactics_Types.witness
                                                    =
                                                    (uu___116_7466.FStar_Tactics_Types.witness);
                                                  FStar_Tactics_Types.goal_ty
                                                    = ty1;
                                                  FStar_Tactics_Types.opts =
                                                    (uu___116_7466.FStar_Tactics_Types.opts);
                                                  FStar_Tactics_Types.is_guard
                                                    =
                                                    (uu___116_7466.FStar_Tactics_Types.is_guard)
                                                })
                                           else fail "not convertible")))))))
       in
    FStar_All.pipe_left (wrap_err "change") uu____7391
  
let (goal_of_goal_ty :
  env ->
    FStar_Syntax_Syntax.typ ->
      (FStar_Tactics_Types.goal,FStar_TypeChecker_Env.guard_t)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun typ  ->
      let uu____7486 =
        FStar_TypeChecker_Util.new_implicit_var "proofstate_of_goal_ty"
          typ.FStar_Syntax_Syntax.pos env typ
         in
      match uu____7486 with
      | (u,uu____7504,g_u) ->
          let g =
            let uu____7519 = FStar_Options.peek ()  in
            {
              FStar_Tactics_Types.context = env;
              FStar_Tactics_Types.witness = u;
              FStar_Tactics_Types.goal_ty = typ;
              FStar_Tactics_Types.opts = uu____7519;
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
      let uu____7530 = goal_of_goal_ty env typ  in
      match uu____7530 with
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
  