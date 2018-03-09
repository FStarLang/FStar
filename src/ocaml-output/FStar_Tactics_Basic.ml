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
              FStar_Util.format1 "Position: %s\n" uu____287  in
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
              let uu____419 =
                FStar_Range.json_of_def_range
                  ps.FStar_Tactics_Types.entry_range
                 in
              ("position", uu____419)  in
            let uu____420 =
              let uu____427 =
                let uu____432 =
                  let uu____433 =
                    FStar_List.map goal_to_json ps.FStar_Tactics_Types.goals
                     in
                  FStar_Util.JsonList uu____433  in
                ("goals", uu____432)  in
              let uu____436 =
                let uu____443 =
                  let uu____448 =
                    let uu____449 =
                      FStar_List.map goal_to_json
                        ps.FStar_Tactics_Types.smt_goals
                       in
                    FStar_Util.JsonList uu____449  in
                  ("smt-goals", uu____448)  in
                [uu____443]  in
              uu____427 :: uu____436  in
            uu____414 :: uu____420  in
          ("label", (FStar_Util.JsonStr msg)) :: uu____407  in
        FStar_Util.JsonAssoc uu____400
  
let (dump_proofstate :
  FStar_Tactics_Types.proofstate -> Prims.string -> Prims.unit) =
  fun ps  ->
    fun msg  ->
      FStar_Options.with_saved_options
        (fun uu____480  ->
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
         (let uu____501 = FStar_Tactics_Types.subst_proof_state subst1 ps  in
          dump_cur uu____501 msg);
         FStar_Tactics_Result.Success ((), ps))
  
let (print_proof_state : Prims.string -> Prims.unit tac) =
  fun msg  ->
    mk_tac
      (fun ps  ->
         let psc = ps.FStar_Tactics_Types.psc  in
         let subst1 = FStar_TypeChecker_Normalize.psc_subst psc  in
         (let uu____517 = FStar_Tactics_Types.subst_proof_state subst1 ps  in
          dump_proofstate uu____517 msg);
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
      let uu____552 = FStar_ST.op_Bang tac_verb_dbg  in
      match uu____552 with
      | FStar_Pervasives_Native.None  ->
          ((let uu____579 =
              let uu____582 =
                FStar_TypeChecker_Env.debug
                  ps.FStar_Tactics_Types.main_context
                  (FStar_Options.Other "TacVerbose")
                 in
              FStar_Pervasives_Native.Some uu____582  in
            FStar_ST.op_Colon_Equals tac_verb_dbg uu____579);
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
         (let uu____651 =
            FStar_TypeChecker_Env.debug ps.FStar_Tactics_Types.main_context
              (FStar_Options.Other "TacFail")
             in
          if uu____651
          then dump_proofstate ps (Prims.strcat "TACTING FAILING: " msg)
          else ());
         FStar_Tactics_Result.Failed (msg, ps))
  
let fail1 : 'Auu____656 . Prims.string -> Prims.string -> 'Auu____656 tac =
  fun msg  ->
    fun x  -> let uu____667 = FStar_Util.format1 msg x  in fail uu____667
  
let fail2 :
  'Auu____672 .
    Prims.string -> Prims.string -> Prims.string -> 'Auu____672 tac
  =
  fun msg  ->
    fun x  ->
      fun y  -> let uu____687 = FStar_Util.format2 msg x y  in fail uu____687
  
let fail3 :
  'Auu____693 .
    Prims.string ->
      Prims.string -> Prims.string -> Prims.string -> 'Auu____693 tac
  =
  fun msg  ->
    fun x  ->
      fun y  ->
        fun z  ->
          let uu____712 = FStar_Util.format3 msg x y z  in fail uu____712
  
let fail4 :
  'Auu____719 .
    Prims.string ->
      Prims.string ->
        Prims.string -> Prims.string -> Prims.string -> 'Auu____719 tac
  =
  fun msg  ->
    fun x  ->
      fun y  ->
        fun z  ->
          fun w  ->
            let uu____742 = FStar_Util.format4 msg x y z w  in fail uu____742
  
let trytac' : 'a . 'a tac -> (Prims.string,'a) FStar_Util.either tac =
  fun t  ->
    mk_tac
      (fun ps  ->
         let tx = FStar_Syntax_Unionfind.new_transaction ()  in
         let uu____772 = run t ps  in
         match uu____772 with
         | FStar_Tactics_Result.Success (a,q) ->
             (FStar_Syntax_Unionfind.commit tx;
              FStar_Tactics_Result.Success ((FStar_Util.Inr a), q))
         | FStar_Tactics_Result.Failed (m,uu____793) ->
             (FStar_Syntax_Unionfind.rollback tx;
              FStar_Tactics_Result.Success ((FStar_Util.Inl m), ps)))
  
let trytac : 'a . 'a tac -> 'a FStar_Pervasives_Native.option tac =
  fun t  ->
    let uu____818 = trytac' t  in
    bind uu____818
      (fun r  ->
         match r with
         | FStar_Util.Inr v1 -> ret (FStar_Pervasives_Native.Some v1)
         | FStar_Util.Inl uu____845 -> ret FStar_Pervasives_Native.None)
  
let wrap_err : 'a . Prims.string -> 'a tac -> 'a tac =
  fun pref  ->
    fun t  ->
      mk_tac
        (fun ps  ->
           let uu____871 = run t ps  in
           match uu____871 with
           | FStar_Tactics_Result.Success (a,q) ->
               FStar_Tactics_Result.Success (a, q)
           | FStar_Tactics_Result.Failed (msg,q) ->
               FStar_Tactics_Result.Failed
                 ((Prims.strcat pref (Prims.strcat ": " msg)), q))
  
let (set : FStar_Tactics_Types.proofstate -> Prims.unit tac) =
  fun p  -> mk_tac (fun uu____888  -> FStar_Tactics_Result.Success ((), p)) 
let (do_unify :
  env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let debug_on uu____901 =
          let uu____902 =
            FStar_Options.set_options FStar_Options.Set
              "--debug_level Rel --debug_level RelCheck"
             in
          ()  in
        let debug_off uu____906 =
          let uu____907 = FStar_Options.set_options FStar_Options.Reset ""
             in
          ()  in
        (let uu____909 =
           FStar_TypeChecker_Env.debug env (FStar_Options.Other "1346")  in
         if uu____909
         then
           (debug_on ();
            (let uu____911 = FStar_Syntax_Print.term_to_string t1  in
             let uu____912 = FStar_Syntax_Print.term_to_string t2  in
             FStar_Util.print2 "%%%%%%%%do_unify %s =? %s\n" uu____911
               uu____912))
         else ());
        (try
           let res = FStar_TypeChecker_Rel.teq_nosmt env t1 t2  in
           debug_off (); res
         with | uu____924 -> (debug_off (); false))
  
let (trysolve :
  FStar_Tactics_Types.goal -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun goal  ->
    fun solution  ->
      do_unify goal.FStar_Tactics_Types.context solution
        goal.FStar_Tactics_Types.witness
  
let (dismiss : Prims.unit tac) =
  bind get
    (fun p  ->
       let uu____937 =
         let uu___61_938 = p  in
         let uu____939 = FStar_List.tl p.FStar_Tactics_Types.goals  in
         {
           FStar_Tactics_Types.main_context =
             (uu___61_938.FStar_Tactics_Types.main_context);
           FStar_Tactics_Types.main_goal =
             (uu___61_938.FStar_Tactics_Types.main_goal);
           FStar_Tactics_Types.all_implicits =
             (uu___61_938.FStar_Tactics_Types.all_implicits);
           FStar_Tactics_Types.goals = uu____939;
           FStar_Tactics_Types.smt_goals =
             (uu___61_938.FStar_Tactics_Types.smt_goals);
           FStar_Tactics_Types.depth =
             (uu___61_938.FStar_Tactics_Types.depth);
           FStar_Tactics_Types.__dump =
             (uu___61_938.FStar_Tactics_Types.__dump);
           FStar_Tactics_Types.psc = (uu___61_938.FStar_Tactics_Types.psc);
           FStar_Tactics_Types.entry_range =
             (uu___61_938.FStar_Tactics_Types.entry_range)
         }  in
       set uu____937)
  
let (solve :
  FStar_Tactics_Types.goal -> FStar_Syntax_Syntax.term -> Prims.unit tac) =
  fun goal  ->
    fun solution  ->
      let uu____952 = trysolve goal solution  in
      if uu____952
      then dismiss
      else
        (let uu____956 =
           let uu____957 = tts goal.FStar_Tactics_Types.context solution  in
           let uu____958 =
             tts goal.FStar_Tactics_Types.context
               goal.FStar_Tactics_Types.witness
              in
           let uu____959 =
             tts goal.FStar_Tactics_Types.context
               goal.FStar_Tactics_Types.goal_ty
              in
           FStar_Util.format3 "%s does not solve %s : %s" uu____957 uu____958
             uu____959
            in
         fail uu____956)
  
let (dismiss_all : Prims.unit tac) =
  bind get
    (fun p  ->
       set
         (let uu___62_966 = p  in
          {
            FStar_Tactics_Types.main_context =
              (uu___62_966.FStar_Tactics_Types.main_context);
            FStar_Tactics_Types.main_goal =
              (uu___62_966.FStar_Tactics_Types.main_goal);
            FStar_Tactics_Types.all_implicits =
              (uu___62_966.FStar_Tactics_Types.all_implicits);
            FStar_Tactics_Types.goals = [];
            FStar_Tactics_Types.smt_goals =
              (uu___62_966.FStar_Tactics_Types.smt_goals);
            FStar_Tactics_Types.depth =
              (uu___62_966.FStar_Tactics_Types.depth);
            FStar_Tactics_Types.__dump =
              (uu___62_966.FStar_Tactics_Types.__dump);
            FStar_Tactics_Types.psc = (uu___62_966.FStar_Tactics_Types.psc);
            FStar_Tactics_Types.entry_range =
              (uu___62_966.FStar_Tactics_Types.entry_range)
          }))
  
let (nwarn : Prims.int FStar_ST.ref) =
  FStar_Util.mk_ref (Prims.parse_int "0") 
let (check_valid_goal : FStar_Tactics_Types.goal -> Prims.unit) =
  fun g  ->
    let uu____983 = FStar_Options.defensive ()  in
    if uu____983
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
        let uu____995 = FStar_TypeChecker_Env.pop_bv e  in
        match uu____995 with
        | FStar_Pervasives_Native.None  -> b3
        | FStar_Pervasives_Native.Some (bv,e1) ->
            let b4 =
              b3 &&
                (FStar_TypeChecker_Env.closed e1 bv.FStar_Syntax_Syntax.sort)
               in
            aux b4 e1
         in
      let uu____1013 =
        (let uu____1016 = aux b2 env  in Prims.op_Negation uu____1016) &&
          (let uu____1018 = FStar_ST.op_Bang nwarn  in
           uu____1018 < (Prims.parse_int "5"))
         in
      (if uu____1013
       then
         ((let uu____1039 =
             let uu____1044 =
               let uu____1045 = goal_to_string g  in
               FStar_Util.format1
                 "The following goal is ill-formed. Keeping calm and carrying on...\n<%s>\n\n"
                 uu____1045
                in
             (FStar_Errors.Warning_IllFormedGoal, uu____1044)  in
           FStar_Errors.log_issue
             (g.FStar_Tactics_Types.goal_ty).FStar_Syntax_Syntax.pos
             uu____1039);
          (let uu____1046 =
             let uu____1047 = FStar_ST.op_Bang nwarn  in
             uu____1047 + (Prims.parse_int "1")  in
           FStar_ST.op_Colon_Equals nwarn uu____1046))
       else ())
    else ()
  
let (add_goals : FStar_Tactics_Types.goal Prims.list -> Prims.unit tac) =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___63_1105 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___63_1105.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___63_1105.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___63_1105.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (FStar_List.append gs p.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___63_1105.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___63_1105.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___63_1105.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___63_1105.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___63_1105.FStar_Tactics_Types.entry_range)
            }))
  
let (add_smt_goals : FStar_Tactics_Types.goal Prims.list -> Prims.unit tac) =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___64_1123 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___64_1123.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___64_1123.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___64_1123.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___64_1123.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (FStar_List.append gs p.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___64_1123.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___64_1123.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___64_1123.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___64_1123.FStar_Tactics_Types.entry_range)
            }))
  
let (push_goals : FStar_Tactics_Types.goal Prims.list -> Prims.unit tac) =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___65_1141 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___65_1141.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___65_1141.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___65_1141.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (FStar_List.append p.FStar_Tactics_Types.goals gs);
              FStar_Tactics_Types.smt_goals =
                (uu___65_1141.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___65_1141.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___65_1141.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___65_1141.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___65_1141.FStar_Tactics_Types.entry_range)
            }))
  
let (push_smt_goals : FStar_Tactics_Types.goal Prims.list -> Prims.unit tac)
  =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___66_1159 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___66_1159.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___66_1159.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___66_1159.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___66_1159.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (FStar_List.append p.FStar_Tactics_Types.smt_goals gs);
              FStar_Tactics_Types.depth =
                (uu___66_1159.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___66_1159.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___66_1159.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___66_1159.FStar_Tactics_Types.entry_range)
            }))
  
let (replace_cur : FStar_Tactics_Types.goal -> Prims.unit tac) =
  fun g  -> bind dismiss (fun uu____1168  -> add_goals [g]) 
let (add_implicits : implicits -> Prims.unit tac) =
  fun i  ->
    bind get
      (fun p  ->
         set
           (let uu___67_1180 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___67_1180.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___67_1180.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (FStar_List.append i p.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___67_1180.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___67_1180.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___67_1180.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___67_1180.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___67_1180.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___67_1180.FStar_Tactics_Types.entry_range)
            }))
  
let (new_uvar :
  Prims.string ->
    env -> FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.term tac)
  =
  fun reason  ->
    fun env  ->
      fun typ  ->
        let uu____1206 =
          FStar_TypeChecker_Util.new_implicit_var reason
            typ.FStar_Syntax_Syntax.pos env typ
           in
        match uu____1206 with
        | (u,uu____1222,g_u) ->
            let uu____1236 =
              add_implicits g_u.FStar_TypeChecker_Env.implicits  in
            bind uu____1236 (fun uu____1240  -> ret u)
  
let (is_true : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____1244 = FStar_Syntax_Util.un_squash t  in
    match uu____1244 with
    | FStar_Pervasives_Native.Some t' ->
        let uu____1254 =
          let uu____1255 = FStar_Syntax_Subst.compress t'  in
          uu____1255.FStar_Syntax_Syntax.n  in
        (match uu____1254 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.true_lid
         | uu____1259 -> false)
    | uu____1260 -> false
  
let (is_false : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____1268 = FStar_Syntax_Util.un_squash t  in
    match uu____1268 with
    | FStar_Pervasives_Native.Some t' ->
        let uu____1278 =
          let uu____1279 = FStar_Syntax_Subst.compress t'  in
          uu____1279.FStar_Syntax_Syntax.n  in
        (match uu____1278 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.false_lid
         | uu____1283 -> false)
    | uu____1284 -> false
  
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
            let uu____1324 = env.FStar_TypeChecker_Env.universe_of env phi
               in
            FStar_Syntax_Util.mk_squash uu____1324 phi  in
          let uu____1325 = new_uvar reason env typ  in
          bind uu____1325
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
             let uu____1381 =
               (ps.FStar_Tactics_Types.main_context).FStar_TypeChecker_Env.type_of
                 e t
                in
             ret uu____1381
           with
           | ex ->
               let uu____1408 = tts e t  in
               let uu____1409 =
                 let uu____1410 = FStar_TypeChecker_Env.all_binders e  in
                 FStar_All.pipe_right uu____1410
                   (FStar_Syntax_Print.binders_to_string ", ")
                  in
               fail2 "Cannot type %s in context (%s)" uu____1408 uu____1409)
  
let (must_trivial : env -> FStar_TypeChecker_Env.guard_t -> Prims.unit tac) =
  fun e  ->
    fun g  ->
      try
        let uu____1434 =
          let uu____1435 =
            let uu____1436 = FStar_TypeChecker_Rel.discharge_guard_no_smt e g
               in
            FStar_All.pipe_left FStar_TypeChecker_Rel.is_trivial uu____1436
             in
          Prims.op_Negation uu____1435  in
        if uu____1434 then fail "got non-trivial guard" else ret ()
      with | uu____1445 -> fail "got non-trivial guard"
  
let (tc : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.typ tac) =
  fun t  ->
    let uu____1453 =
      bind cur_goal
        (fun goal  ->
           let uu____1459 = __tc goal.FStar_Tactics_Types.context t  in
           bind uu____1459
             (fun uu____1479  ->
                match uu____1479 with
                | (t1,typ,guard) ->
                    let uu____1491 =
                      must_trivial goal.FStar_Tactics_Types.context guard  in
                    bind uu____1491 (fun uu____1495  -> ret typ)))
       in
    FStar_All.pipe_left (wrap_err "tc") uu____1453
  
let (add_irrelevant_goal :
  Prims.string ->
    env ->
      FStar_Syntax_Syntax.typ -> FStar_Options.optionstate -> Prims.unit tac)
  =
  fun reason  ->
    fun env  ->
      fun phi  ->
        fun opts  ->
          let uu____1516 = mk_irrelevant_goal reason env phi opts  in
          bind uu____1516 (fun goal  -> add_goals [goal])
  
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
       let uu____1538 =
         istrivial goal.FStar_Tactics_Types.context
           goal.FStar_Tactics_Types.goal_ty
          in
       if uu____1538
       then solve goal FStar_Syntax_Util.exp_unit
       else
         (let uu____1542 =
            tts goal.FStar_Tactics_Types.context
              goal.FStar_Tactics_Types.goal_ty
             in
          fail1 "Not a trivial goal: %s" uu____1542))
  
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
          let uu____1559 =
            let uu____1560 = FStar_TypeChecker_Rel.simplify_guard e g  in
            uu____1560.FStar_TypeChecker_Env.guard_f  in
          match uu____1559 with
          | FStar_TypeChecker_Common.Trivial  -> ret ()
          | FStar_TypeChecker_Common.NonTrivial f ->
              let uu____1564 = istrivial e f  in
              if uu____1564
              then ret ()
              else
                (let uu____1568 = mk_irrelevant_goal reason e f opts  in
                 bind uu____1568
                   (fun goal  ->
                      let goal1 =
                        let uu___72_1575 = goal  in
                        {
                          FStar_Tactics_Types.context =
                            (uu___72_1575.FStar_Tactics_Types.context);
                          FStar_Tactics_Types.witness =
                            (uu___72_1575.FStar_Tactics_Types.witness);
                          FStar_Tactics_Types.goal_ty =
                            (uu___72_1575.FStar_Tactics_Types.goal_ty);
                          FStar_Tactics_Types.opts =
                            (uu___72_1575.FStar_Tactics_Types.opts);
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
          let uu____1596 =
            let uu____1597 = FStar_TypeChecker_Rel.simplify_guard e g  in
            uu____1597.FStar_TypeChecker_Env.guard_f  in
          match uu____1596 with
          | FStar_TypeChecker_Common.Trivial  ->
              ret FStar_Pervasives_Native.None
          | FStar_TypeChecker_Common.NonTrivial f ->
              let uu____1605 = istrivial e f  in
              if uu____1605
              then ret FStar_Pervasives_Native.None
              else
                (let uu____1613 = mk_irrelevant_goal reason e f opts  in
                 bind uu____1613
                   (fun goal  ->
                      ret
                        (FStar_Pervasives_Native.Some
                           (let uu___73_1623 = goal  in
                            {
                              FStar_Tactics_Types.context =
                                (uu___73_1623.FStar_Tactics_Types.context);
                              FStar_Tactics_Types.witness =
                                (uu___73_1623.FStar_Tactics_Types.witness);
                              FStar_Tactics_Types.goal_ty =
                                (uu___73_1623.FStar_Tactics_Types.goal_ty);
                              FStar_Tactics_Types.opts =
                                (uu___73_1623.FStar_Tactics_Types.opts);
                              FStar_Tactics_Types.is_guard = true
                            }))))
  
let (smt : Prims.unit tac) =
  bind cur_goal
    (fun g  ->
       let uu____1631 = is_irrelevant g  in
       if uu____1631
       then bind dismiss (fun uu____1635  -> add_smt_goals [g])
       else
         (let uu____1637 =
            tts g.FStar_Tactics_Types.context g.FStar_Tactics_Types.goal_ty
             in
          fail1 "goal is not irrelevant: cannot dispatch to smt (%s)"
            uu____1637))
  
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
             let uu____1678 =
               try
                 let uu____1712 =
                   let uu____1721 = FStar_BigInt.to_int_fs n1  in
                   FStar_List.splitAt uu____1721 p.FStar_Tactics_Types.goals
                    in
                 ret uu____1712
               with | uu____1743 -> fail "divide: not enough goals"  in
             bind uu____1678
               (fun uu____1770  ->
                  match uu____1770 with
                  | (lgs,rgs) ->
                      let lp =
                        let uu___74_1796 = p  in
                        {
                          FStar_Tactics_Types.main_context =
                            (uu___74_1796.FStar_Tactics_Types.main_context);
                          FStar_Tactics_Types.main_goal =
                            (uu___74_1796.FStar_Tactics_Types.main_goal);
                          FStar_Tactics_Types.all_implicits =
                            (uu___74_1796.FStar_Tactics_Types.all_implicits);
                          FStar_Tactics_Types.goals = lgs;
                          FStar_Tactics_Types.smt_goals = [];
                          FStar_Tactics_Types.depth =
                            (uu___74_1796.FStar_Tactics_Types.depth);
                          FStar_Tactics_Types.__dump =
                            (uu___74_1796.FStar_Tactics_Types.__dump);
                          FStar_Tactics_Types.psc =
                            (uu___74_1796.FStar_Tactics_Types.psc);
                          FStar_Tactics_Types.entry_range =
                            (uu___74_1796.FStar_Tactics_Types.entry_range)
                        }  in
                      let rp =
                        let uu___75_1798 = p  in
                        {
                          FStar_Tactics_Types.main_context =
                            (uu___75_1798.FStar_Tactics_Types.main_context);
                          FStar_Tactics_Types.main_goal =
                            (uu___75_1798.FStar_Tactics_Types.main_goal);
                          FStar_Tactics_Types.all_implicits =
                            (uu___75_1798.FStar_Tactics_Types.all_implicits);
                          FStar_Tactics_Types.goals = rgs;
                          FStar_Tactics_Types.smt_goals = [];
                          FStar_Tactics_Types.depth =
                            (uu___75_1798.FStar_Tactics_Types.depth);
                          FStar_Tactics_Types.__dump =
                            (uu___75_1798.FStar_Tactics_Types.__dump);
                          FStar_Tactics_Types.psc =
                            (uu___75_1798.FStar_Tactics_Types.psc);
                          FStar_Tactics_Types.entry_range =
                            (uu___75_1798.FStar_Tactics_Types.entry_range)
                        }  in
                      let uu____1799 = set lp  in
                      bind uu____1799
                        (fun uu____1807  ->
                           bind l
                             (fun a  ->
                                bind get
                                  (fun lp'  ->
                                     let uu____1821 = set rp  in
                                     bind uu____1821
                                       (fun uu____1829  ->
                                          bind r
                                            (fun b  ->
                                               bind get
                                                 (fun rp'  ->
                                                    let p' =
                                                      let uu___76_1845 = p
                                                         in
                                                      {
                                                        FStar_Tactics_Types.main_context
                                                          =
                                                          (uu___76_1845.FStar_Tactics_Types.main_context);
                                                        FStar_Tactics_Types.main_goal
                                                          =
                                                          (uu___76_1845.FStar_Tactics_Types.main_goal);
                                                        FStar_Tactics_Types.all_implicits
                                                          =
                                                          (uu___76_1845.FStar_Tactics_Types.all_implicits);
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
                                                          (uu___76_1845.FStar_Tactics_Types.depth);
                                                        FStar_Tactics_Types.__dump
                                                          =
                                                          (uu___76_1845.FStar_Tactics_Types.__dump);
                                                        FStar_Tactics_Types.psc
                                                          =
                                                          (uu___76_1845.FStar_Tactics_Types.psc);
                                                        FStar_Tactics_Types.entry_range
                                                          =
                                                          (uu___76_1845.FStar_Tactics_Types.entry_range)
                                                      }  in
                                                    let uu____1846 = set p'
                                                       in
                                                    bind uu____1846
                                                      (fun uu____1854  ->
                                                         ret (a, b))))))))))
  
let focus : 'a . 'a tac -> 'a tac =
  fun f  ->
    let uu____1872 = divide FStar_BigInt.one f idtac  in
    bind uu____1872
      (fun uu____1885  -> match uu____1885 with | (a,()) -> ret a)
  
let rec map : 'a . 'a tac -> 'a Prims.list tac =
  fun tau  ->
    bind get
      (fun p  ->
         match p.FStar_Tactics_Types.goals with
         | [] -> ret []
         | uu____1919::uu____1920 ->
             let uu____1923 =
               let uu____1932 = map tau  in
               divide FStar_BigInt.one tau uu____1932  in
             bind uu____1923
               (fun uu____1950  ->
                  match uu____1950 with | (h,t) -> ret (h :: t)))
  
let (seq : Prims.unit tac -> Prims.unit tac -> Prims.unit tac) =
  fun t1  ->
    fun t2  ->
      let uu____1987 =
        bind t1
          (fun uu____1992  ->
             let uu____1993 = map t2  in
             bind uu____1993 (fun uu____2001  -> ret ()))
         in
      focus uu____1987
  
let (intro : FStar_Syntax_Syntax.binder tac) =
  let uu____2008 =
    bind cur_goal
      (fun goal  ->
         let uu____2017 =
           FStar_Syntax_Util.arrow_one goal.FStar_Tactics_Types.goal_ty  in
         match uu____2017 with
         | FStar_Pervasives_Native.Some (b,c) ->
             let uu____2032 =
               let uu____2033 = FStar_Syntax_Util.is_total_comp c  in
               Prims.op_Negation uu____2033  in
             if uu____2032
             then fail "Codomain is effectful"
             else
               (let env' =
                  FStar_TypeChecker_Env.push_binders
                    goal.FStar_Tactics_Types.context [b]
                   in
                let typ' = comp_to_typ c  in
                let uu____2039 = new_uvar "intro" env' typ'  in
                bind uu____2039
                  (fun u  ->
                     let uu____2046 =
                       let uu____2047 =
                         FStar_Syntax_Util.abs [b] u
                           FStar_Pervasives_Native.None
                          in
                       trysolve goal uu____2047  in
                     if uu____2046
                     then
                       let uu____2050 =
                         let uu____2053 =
                           let uu___79_2054 = goal  in
                           let uu____2055 = bnorm env' u  in
                           let uu____2056 = bnorm env' typ'  in
                           {
                             FStar_Tactics_Types.context = env';
                             FStar_Tactics_Types.witness = uu____2055;
                             FStar_Tactics_Types.goal_ty = uu____2056;
                             FStar_Tactics_Types.opts =
                               (uu___79_2054.FStar_Tactics_Types.opts);
                             FStar_Tactics_Types.is_guard =
                               (uu___79_2054.FStar_Tactics_Types.is_guard)
                           }  in
                         replace_cur uu____2053  in
                       bind uu____2050 (fun uu____2058  -> ret b)
                     else fail "unification failed"))
         | FStar_Pervasives_Native.None  ->
             let uu____2064 =
               tts goal.FStar_Tactics_Types.context
                 goal.FStar_Tactics_Types.goal_ty
                in
             fail1 "goal is not an arrow (%s)" uu____2064)
     in
  FStar_All.pipe_left (wrap_err "intro") uu____2008 
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
       (let uu____2095 =
          FStar_Syntax_Util.arrow_one goal.FStar_Tactics_Types.goal_ty  in
        match uu____2095 with
        | FStar_Pervasives_Native.Some (b,c) ->
            let uu____2114 =
              let uu____2115 = FStar_Syntax_Util.is_total_comp c  in
              Prims.op_Negation uu____2115  in
            if uu____2114
            then fail "Codomain is effectful"
            else
              (let bv =
                 FStar_Syntax_Syntax.gen_bv "__recf"
                   FStar_Pervasives_Native.None
                   goal.FStar_Tactics_Types.goal_ty
                  in
               let bs =
                 let uu____2131 = FStar_Syntax_Syntax.mk_binder bv  in
                 [uu____2131; b]  in
               let env' =
                 FStar_TypeChecker_Env.push_binders
                   goal.FStar_Tactics_Types.context bs
                  in
               let uu____2133 =
                 let uu____2136 = comp_to_typ c  in
                 new_uvar "intro_rec" env' uu____2136  in
               bind uu____2133
                 (fun u  ->
                    let lb =
                      let uu____2152 =
                        FStar_Syntax_Util.abs [b] u
                          FStar_Pervasives_Native.None
                         in
                      FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl bv) []
                        goal.FStar_Tactics_Types.goal_ty
                        FStar_Parser_Const.effect_Tot_lid uu____2152 []
                        FStar_Range.dummyRange
                       in
                    let body = FStar_Syntax_Syntax.bv_to_name bv  in
                    let uu____2158 =
                      FStar_Syntax_Subst.close_let_rec [lb] body  in
                    match uu____2158 with
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
                          let uu____2195 =
                            let uu____2198 =
                              let uu___80_2199 = goal  in
                              let uu____2200 = bnorm env' u  in
                              let uu____2201 =
                                let uu____2202 = comp_to_typ c  in
                                bnorm env' uu____2202  in
                              {
                                FStar_Tactics_Types.context = env';
                                FStar_Tactics_Types.witness = uu____2200;
                                FStar_Tactics_Types.goal_ty = uu____2201;
                                FStar_Tactics_Types.opts =
                                  (uu___80_2199.FStar_Tactics_Types.opts);
                                FStar_Tactics_Types.is_guard =
                                  (uu___80_2199.FStar_Tactics_Types.is_guard)
                              }  in
                            replace_cur uu____2198  in
                          bind uu____2195
                            (fun uu____2209  ->
                               let uu____2210 =
                                 let uu____2215 =
                                   FStar_Syntax_Syntax.mk_binder bv  in
                                 (uu____2215, b)  in
                               ret uu____2210)
                        else fail "intro_rec: unification failed"))
        | FStar_Pervasives_Native.None  ->
            let uu____2229 =
              tts goal.FStar_Tactics_Types.context
                goal.FStar_Tactics_Types.goal_ty
               in
            fail1 "intro_rec: goal is not an arrow (%s)" uu____2229))
  
let (norm : FStar_Syntax_Embeddings.norm_step Prims.list -> Prims.unit tac) =
  fun s  ->
    bind cur_goal
      (fun goal  ->
         mlog
           (fun uu____2249  ->
              let uu____2250 =
                FStar_Syntax_Print.term_to_string
                  goal.FStar_Tactics_Types.witness
                 in
              FStar_Util.print1 "norm: witness = %s\n" uu____2250)
           (fun uu____2255  ->
              let steps =
                let uu____2259 = FStar_TypeChecker_Normalize.tr_norm_steps s
                   in
                FStar_List.append
                  [FStar_TypeChecker_Normalize.Reify;
                  FStar_TypeChecker_Normalize.UnfoldTac] uu____2259
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
                (let uu___81_2266 = goal  in
                 {
                   FStar_Tactics_Types.context =
                     (uu___81_2266.FStar_Tactics_Types.context);
                   FStar_Tactics_Types.witness = w;
                   FStar_Tactics_Types.goal_ty = t;
                   FStar_Tactics_Types.opts =
                     (uu___81_2266.FStar_Tactics_Types.opts);
                   FStar_Tactics_Types.is_guard =
                     (uu___81_2266.FStar_Tactics_Types.is_guard)
                 })))
  
let (norm_term_env :
  env ->
    FStar_Syntax_Embeddings.norm_step Prims.list ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac)
  =
  fun e  ->
    fun s  ->
      fun t  ->
        let uu____2284 =
          mlog
            (fun uu____2289  ->
               let uu____2290 = FStar_Syntax_Print.term_to_string t  in
               FStar_Util.print1 "norm_term: tm = %s\n" uu____2290)
            (fun uu____2292  ->
               bind get
                 (fun ps  ->
                    mlog
                      (fun uu____2297  ->
                         let uu____2298 =
                           tts ps.FStar_Tactics_Types.main_context t  in
                         FStar_Util.print1 "norm_term_env: t = %s\n"
                           uu____2298)
                      (fun uu____2301  ->
                         let uu____2302 = __tc e t  in
                         bind uu____2302
                           (fun uu____2324  ->
                              match uu____2324 with
                              | (t1,uu____2334,guard) ->
                                  (FStar_TypeChecker_Rel.force_trivial_guard
                                     e guard;
                                   (let steps =
                                      let uu____2340 =
                                        FStar_TypeChecker_Normalize.tr_norm_steps
                                          s
                                         in
                                      FStar_List.append
                                        [FStar_TypeChecker_Normalize.Reify;
                                        FStar_TypeChecker_Normalize.UnfoldTac]
                                        uu____2340
                                       in
                                    let t2 =
                                      normalize steps
                                        ps.FStar_Tactics_Types.main_context
                                        t1
                                       in
                                    ret t2))))))
           in
        FStar_All.pipe_left (wrap_err "norm_term") uu____2284
  
let (refine_intro : Prims.unit tac) =
  let uu____2352 =
    bind cur_goal
      (fun g  ->
         let uu____2359 =
           FStar_TypeChecker_Rel.base_and_refinement
             g.FStar_Tactics_Types.context g.FStar_Tactics_Types.goal_ty
            in
         match uu____2359 with
         | (uu____2372,FStar_Pervasives_Native.None ) ->
             fail "not a refinement"
         | (t,FStar_Pervasives_Native.Some (bv,phi)) ->
             let g1 =
               let uu___82_2397 = g  in
               {
                 FStar_Tactics_Types.context =
                   (uu___82_2397.FStar_Tactics_Types.context);
                 FStar_Tactics_Types.witness =
                   (uu___82_2397.FStar_Tactics_Types.witness);
                 FStar_Tactics_Types.goal_ty = t;
                 FStar_Tactics_Types.opts =
                   (uu___82_2397.FStar_Tactics_Types.opts);
                 FStar_Tactics_Types.is_guard =
                   (uu___82_2397.FStar_Tactics_Types.is_guard)
               }  in
             let uu____2398 =
               let uu____2403 =
                 let uu____2408 =
                   let uu____2409 = FStar_Syntax_Syntax.mk_binder bv  in
                   [uu____2409]  in
                 FStar_Syntax_Subst.open_term uu____2408 phi  in
               match uu____2403 with
               | (bvs,phi1) ->
                   let uu____2416 =
                     let uu____2417 = FStar_List.hd bvs  in
                     FStar_Pervasives_Native.fst uu____2417  in
                   (uu____2416, phi1)
                in
             (match uu____2398 with
              | (bv1,phi1) ->
                  let uu____2430 =
                    let uu____2433 =
                      FStar_Syntax_Subst.subst
                        [FStar_Syntax_Syntax.NT
                           (bv1, (g.FStar_Tactics_Types.witness))] phi1
                       in
                    mk_irrelevant_goal "refine_intro refinement"
                      g.FStar_Tactics_Types.context uu____2433
                      g.FStar_Tactics_Types.opts
                     in
                  bind uu____2430
                    (fun g2  ->
                       bind dismiss (fun uu____2437  -> add_goals [g1; g2]))))
     in
  FStar_All.pipe_left (wrap_err "refine_intro") uu____2352 
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
             let uu____2461 = __tc env t  in
             bind uu____2461
               (fun uu____2481  ->
                  match uu____2481 with
                  | (t1,typ,guard) ->
                      let uu____2493 =
                        if force_guard
                        then
                          must_trivial goal.FStar_Tactics_Types.context guard
                        else
                          add_goal_from_guard "__exact typing"
                            goal.FStar_Tactics_Types.context guard
                            goal.FStar_Tactics_Types.opts
                         in
                      bind uu____2493
                        (fun uu____2500  ->
                           mlog
                             (fun uu____2504  ->
                                let uu____2505 =
                                  tts goal.FStar_Tactics_Types.context typ
                                   in
                                let uu____2506 =
                                  tts goal.FStar_Tactics_Types.context
                                    goal.FStar_Tactics_Types.goal_ty
                                   in
                                FStar_Util.print2
                                  "exact: unifying %s and %s\n" uu____2505
                                  uu____2506)
                             (fun uu____2509  ->
                                let uu____2510 =
                                  do_unify goal.FStar_Tactics_Types.context
                                    typ goal.FStar_Tactics_Types.goal_ty
                                   in
                                if uu____2510
                                then solve goal t1
                                else
                                  (let uu____2514 =
                                     tts goal.FStar_Tactics_Types.context t1
                                      in
                                   let uu____2515 =
                                     tts goal.FStar_Tactics_Types.context typ
                                      in
                                   let uu____2516 =
                                     tts goal.FStar_Tactics_Types.context
                                       goal.FStar_Tactics_Types.goal_ty
                                      in
                                   let uu____2517 =
                                     tts goal.FStar_Tactics_Types.context
                                       goal.FStar_Tactics_Types.witness
                                      in
                                   fail4
                                     "%s : %s does not exactly solve the goal %s (witness = %s)"
                                     uu____2514 uu____2515 uu____2516
                                     uu____2517)))))
  
let (t_exact :
  Prims.bool -> Prims.bool -> FStar_Syntax_Syntax.term -> Prims.unit tac) =
  fun set_expected_typ1  ->
    fun force_guard  ->
      fun tm  ->
        let uu____2531 =
          mlog
            (fun uu____2536  ->
               let uu____2537 = FStar_Syntax_Print.term_to_string tm  in
               FStar_Util.print1 "t_exact: tm = %s\n" uu____2537)
            (fun uu____2540  ->
               let uu____2541 =
                 let uu____2548 =
                   __exact_now set_expected_typ1 force_guard tm  in
                 trytac' uu____2548  in
               bind uu____2541
                 (fun uu___56_2557  ->
                    match uu___56_2557 with
                    | FStar_Util.Inr r -> ret ()
                    | FStar_Util.Inl e ->
                        let uu____2566 =
                          let uu____2573 =
                            let uu____2576 =
                              norm [FStar_Syntax_Embeddings.Delta]  in
                            bind uu____2576
                              (fun uu____2580  ->
                                 bind refine_intro
                                   (fun uu____2582  ->
                                      __exact_now set_expected_typ1
                                        force_guard tm))
                             in
                          trytac' uu____2573  in
                        bind uu____2566
                          (fun uu___55_2589  ->
                             match uu___55_2589 with
                             | FStar_Util.Inr r -> ret ()
                             | FStar_Util.Inl uu____2597 -> fail e)))
           in
        FStar_All.pipe_left (wrap_err "exact") uu____2531
  
let (uvar_free_in_goal :
  FStar_Syntax_Syntax.uvar -> FStar_Tactics_Types.goal -> Prims.bool) =
  fun u  ->
    fun g  ->
      if g.FStar_Tactics_Types.is_guard
      then false
      else
        (let free_uvars =
           let uu____2612 =
             let uu____2619 =
               FStar_Syntax_Free.uvars g.FStar_Tactics_Types.goal_ty  in
             FStar_Util.set_elements uu____2619  in
           FStar_List.map FStar_Pervasives_Native.fst uu____2612  in
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
          let uu____2679 = f x  in
          bind uu____2679
            (fun y  ->
               let uu____2687 = mapM f xs  in
               bind uu____2687 (fun ys  -> ret (y :: ys)))
  
exception NoUnif 
let (uu___is_NoUnif : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with | NoUnif  -> true | uu____2705 -> false
  
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
               (fun uu____2723  ->
                  let uu____2724 = FStar_Syntax_Print.term_to_string tm  in
                  FStar_Util.print1 ">>> Calling __exact(%s)\n" uu____2724)
               (fun uu____2727  ->
                  let uu____2728 =
                    let uu____2733 = t_exact false true tm  in
                    trytac uu____2733  in
                  bind uu____2728
                    (fun uu___57_2740  ->
                       match uu___57_2740 with
                       | FStar_Pervasives_Native.Some r -> ret ()
                       | FStar_Pervasives_Native.None  ->
                           mlog
                             (fun uu____2748  ->
                                let uu____2749 =
                                  FStar_Syntax_Print.term_to_string typ  in
                                FStar_Util.print1 ">>> typ = %s\n" uu____2749)
                             (fun uu____2752  ->
                                let uu____2753 =
                                  FStar_Syntax_Util.arrow_one typ  in
                                match uu____2753 with
                                | FStar_Pervasives_Native.None  ->
                                    FStar_Exn.raise NoUnif
                                | FStar_Pervasives_Native.Some ((bv,aq),c) ->
                                    mlog
                                      (fun uu____2785  ->
                                         let uu____2786 =
                                           FStar_Syntax_Print.binder_to_string
                                             (bv, aq)
                                            in
                                         FStar_Util.print1
                                           "__apply: pushing binder %s\n"
                                           uu____2786)
                                      (fun uu____2789  ->
                                         let uu____2790 =
                                           let uu____2791 =
                                             FStar_Syntax_Util.is_total_comp
                                               c
                                              in
                                           Prims.op_Negation uu____2791  in
                                         if uu____2790
                                         then
                                           fail "apply: not total codomain"
                                         else
                                           (let uu____2795 =
                                              new_uvar "apply"
                                                goal.FStar_Tactics_Types.context
                                                bv.FStar_Syntax_Syntax.sort
                                               in
                                            bind uu____2795
                                              (fun u  ->
                                                 let tm' =
                                                   FStar_Syntax_Syntax.mk_Tm_app
                                                     tm [(u, aq)]
                                                     FStar_Pervasives_Native.None
                                                     tm.FStar_Syntax_Syntax.pos
                                                    in
                                                 let typ' =
                                                   let uu____2815 =
                                                     comp_to_typ c  in
                                                   FStar_All.pipe_left
                                                     (FStar_Syntax_Subst.subst
                                                        [FStar_Syntax_Syntax.NT
                                                           (bv, u)])
                                                     uu____2815
                                                    in
                                                 let uu____2816 =
                                                   __apply uopt tm' typ'  in
                                                 bind uu____2816
                                                   (fun uu____2824  ->
                                                      let u1 =
                                                        bnorm
                                                          goal.FStar_Tactics_Types.context
                                                          u
                                                         in
                                                      let uu____2826 =
                                                        let uu____2827 =
                                                          let uu____2830 =
                                                            let uu____2831 =
                                                              FStar_Syntax_Util.head_and_args
                                                                u1
                                                               in
                                                            FStar_Pervasives_Native.fst
                                                              uu____2831
                                                             in
                                                          FStar_Syntax_Subst.compress
                                                            uu____2830
                                                           in
                                                        uu____2827.FStar_Syntax_Syntax.n
                                                         in
                                                      match uu____2826 with
                                                      | FStar_Syntax_Syntax.Tm_uvar
                                                          (uvar,uu____2859)
                                                          ->
                                                          bind get
                                                            (fun ps  ->
                                                               let uu____2887
                                                                 =
                                                                 uopt &&
                                                                   (uvar_free
                                                                    uvar ps)
                                                                  in
                                                               if uu____2887
                                                               then ret ()
                                                               else
                                                                 (let uu____2891
                                                                    =
                                                                    let uu____2894
                                                                    =
                                                                    let uu___83_2895
                                                                    = goal
                                                                     in
                                                                    let uu____2896
                                                                    =
                                                                    bnorm
                                                                    goal.FStar_Tactics_Types.context
                                                                    u1  in
                                                                    let uu____2897
                                                                    =
                                                                    bnorm
                                                                    goal.FStar_Tactics_Types.context
                                                                    bv.FStar_Syntax_Syntax.sort
                                                                     in
                                                                    {
                                                                    FStar_Tactics_Types.context
                                                                    =
                                                                    (uu___83_2895.FStar_Tactics_Types.context);
                                                                    FStar_Tactics_Types.witness
                                                                    =
                                                                    uu____2896;
                                                                    FStar_Tactics_Types.goal_ty
                                                                    =
                                                                    uu____2897;
                                                                    FStar_Tactics_Types.opts
                                                                    =
                                                                    (uu___83_2895.FStar_Tactics_Types.opts);
                                                                    FStar_Tactics_Types.is_guard
                                                                    = false
                                                                    }  in
                                                                    [uu____2894]
                                                                     in
                                                                  add_goals
                                                                    uu____2891))
                                                      | t -> ret ()))))))))
  
let try_unif : 'a . 'a tac -> 'a tac -> 'a tac =
  fun t  ->
    fun t'  -> mk_tac (fun ps  -> try run t ps with | NoUnif  -> run t' ps)
  
let (apply : Prims.bool -> FStar_Syntax_Syntax.term -> Prims.unit tac) =
  fun uopt  ->
    fun tm  ->
      let uu____2943 =
        mlog
          (fun uu____2948  ->
             let uu____2949 = FStar_Syntax_Print.term_to_string tm  in
             FStar_Util.print1 "apply: tm = %s\n" uu____2949)
          (fun uu____2951  ->
             bind cur_goal
               (fun goal  ->
                  let uu____2955 = __tc goal.FStar_Tactics_Types.context tm
                     in
                  bind uu____2955
                    (fun uu____2976  ->
                       match uu____2976 with
                       | (tm1,typ,guard) ->
                           let uu____2988 =
                             let uu____2991 =
                               let uu____2994 = __apply uopt tm1 typ  in
                               bind uu____2994
                                 (fun uu____2998  ->
                                    add_goal_from_guard "apply guard"
                                      goal.FStar_Tactics_Types.context guard
                                      goal.FStar_Tactics_Types.opts)
                                in
                             focus uu____2991  in
                           let uu____2999 =
                             let uu____3002 =
                               tts goal.FStar_Tactics_Types.context tm1  in
                             let uu____3003 =
                               tts goal.FStar_Tactics_Types.context typ  in
                             let uu____3004 =
                               tts goal.FStar_Tactics_Types.context
                                 goal.FStar_Tactics_Types.goal_ty
                                in
                             fail3
                               "Cannot instantiate %s (of type %s) to match goal (%s)"
                               uu____3002 uu____3003 uu____3004
                              in
                           try_unif uu____2988 uu____2999)))
         in
      FStar_All.pipe_left (wrap_err "apply") uu____2943
  
let (apply_lemma : FStar_Syntax_Syntax.term -> Prims.unit tac) =
  fun tm  ->
    let uu____3016 =
      let uu____3019 =
        mlog
          (fun uu____3024  ->
             let uu____3025 = FStar_Syntax_Print.term_to_string tm  in
             FStar_Util.print1 "apply_lemma: tm = %s\n" uu____3025)
          (fun uu____3028  ->
             let is_unit_t t =
               let uu____3033 =
                 let uu____3034 = FStar_Syntax_Subst.compress t  in
                 uu____3034.FStar_Syntax_Syntax.n  in
               match uu____3033 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.unit_lid
                   -> true
               | uu____3038 -> false  in
             bind cur_goal
               (fun goal  ->
                  let uu____3042 = __tc goal.FStar_Tactics_Types.context tm
                     in
                  bind uu____3042
                    (fun uu____3064  ->
                       match uu____3064 with
                       | (tm1,t,guard) ->
                           let uu____3076 =
                             FStar_Syntax_Util.arrow_formals_comp t  in
                           (match uu____3076 with
                            | (bs,comp) ->
                                if
                                  Prims.op_Negation
                                    (FStar_Syntax_Util.is_lemma_comp comp)
                                then fail "not a lemma"
                                else
                                  (let uu____3106 =
                                     FStar_List.fold_left
                                       (fun uu____3152  ->
                                          fun uu____3153  ->
                                            match (uu____3152, uu____3153)
                                            with
                                            | ((uvs,guard1,subst1),(b,aq)) ->
                                                let b_t =
                                                  FStar_Syntax_Subst.subst
                                                    subst1
                                                    b.FStar_Syntax_Syntax.sort
                                                   in
                                                let uu____3256 =
                                                  is_unit_t b_t  in
                                                if uu____3256
                                                then
                                                  (((FStar_Syntax_Util.exp_unit,
                                                      aq) :: uvs), guard1,
                                                    ((FStar_Syntax_Syntax.NT
                                                        (b,
                                                          FStar_Syntax_Util.exp_unit))
                                                    :: subst1))
                                                else
                                                  (let uu____3294 =
                                                     FStar_TypeChecker_Util.new_implicit_var
                                                       "apply_lemma"
                                                       (goal.FStar_Tactics_Types.goal_ty).FStar_Syntax_Syntax.pos
                                                       goal.FStar_Tactics_Types.context
                                                       b_t
                                                      in
                                                   match uu____3294 with
                                                   | (u,uu____3324,g_u) ->
                                                       let uu____3338 =
                                                         FStar_TypeChecker_Rel.conj_guard
                                                           guard1 g_u
                                                          in
                                                       (((u, aq) :: uvs),
                                                         uu____3338,
                                                         ((FStar_Syntax_Syntax.NT
                                                             (b, u)) ::
                                                         subst1))))
                                       ([], guard, []) bs
                                      in
                                   match uu____3106 with
                                   | (uvs,implicits,subst1) ->
                                       let uvs1 = FStar_List.rev uvs  in
                                       let comp1 =
                                         FStar_Syntax_Subst.subst_comp subst1
                                           comp
                                          in
                                       let uu____3408 =
                                         let uu____3417 =
                                           let uu____3426 =
                                             FStar_Syntax_Util.comp_to_comp_typ
                                               comp1
                                              in
                                           uu____3426.FStar_Syntax_Syntax.effect_args
                                            in
                                         match uu____3417 with
                                         | pre::post::uu____3437 ->
                                             ((FStar_Pervasives_Native.fst
                                                 pre),
                                               (FStar_Pervasives_Native.fst
                                                  post))
                                         | uu____3478 ->
                                             failwith
                                               "apply_lemma: impossible: not a lemma"
                                          in
                                       (match uu____3408 with
                                        | (pre,post) ->
                                            let post1 =
                                              let uu____3510 =
                                                let uu____3519 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    FStar_Syntax_Util.exp_unit
                                                   in
                                                [uu____3519]  in
                                              FStar_Syntax_Util.mk_app post
                                                uu____3510
                                               in
                                            let uu____3520 =
                                              let uu____3521 =
                                                let uu____3522 =
                                                  FStar_Syntax_Util.mk_squash
                                                    FStar_Syntax_Syntax.U_zero
                                                    post1
                                                   in
                                                do_unify
                                                  goal.FStar_Tactics_Types.context
                                                  uu____3522
                                                  goal.FStar_Tactics_Types.goal_ty
                                                 in
                                              Prims.op_Negation uu____3521
                                               in
                                            if uu____3520
                                            then
                                              let uu____3525 =
                                                tts
                                                  goal.FStar_Tactics_Types.context
                                                  tm1
                                                 in
                                              let uu____3526 =
                                                let uu____3527 =
                                                  FStar_Syntax_Util.mk_squash
                                                    FStar_Syntax_Syntax.U_zero
                                                    post1
                                                   in
                                                tts
                                                  goal.FStar_Tactics_Types.context
                                                  uu____3527
                                                 in
                                              let uu____3528 =
                                                tts
                                                  goal.FStar_Tactics_Types.context
                                                  goal.FStar_Tactics_Types.goal_ty
                                                 in
                                              fail3
                                                "Cannot instantiate lemma %s (with postcondition: %s) to match goal (%s)"
                                                uu____3525 uu____3526
                                                uu____3528
                                            else
                                              (let uu____3530 =
                                                 add_implicits
                                                   implicits.FStar_TypeChecker_Env.implicits
                                                  in
                                               bind uu____3530
                                                 (fun uu____3535  ->
                                                    let uu____3536 =
                                                      solve goal
                                                        FStar_Syntax_Util.exp_unit
                                                       in
                                                    bind uu____3536
                                                      (fun uu____3544  ->
                                                         let is_free_uvar uv
                                                           t1 =
                                                           let free_uvars =
                                                             let uu____3555 =
                                                               let uu____3562
                                                                 =
                                                                 FStar_Syntax_Free.uvars
                                                                   t1
                                                                  in
                                                               FStar_Util.set_elements
                                                                 uu____3562
                                                                in
                                                             FStar_List.map
                                                               FStar_Pervasives_Native.fst
                                                               uu____3555
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
                                                           let uu____3603 =
                                                             FStar_Syntax_Util.head_and_args
                                                               t1
                                                              in
                                                           match uu____3603
                                                           with
                                                           | (hd1,uu____3619)
                                                               ->
                                                               (match 
                                                                  hd1.FStar_Syntax_Syntax.n
                                                                with
                                                                | FStar_Syntax_Syntax.Tm_uvar
                                                                    (uv,uu____3641)
                                                                    ->
                                                                    appears
                                                                    uv goals
                                                                | uu____3666
                                                                    -> false)
                                                            in
                                                         let uu____3667 =
                                                           FStar_All.pipe_right
                                                             implicits.FStar_TypeChecker_Env.implicits
                                                             (mapM
                                                                (fun
                                                                   uu____3739
                                                                    ->
                                                                   match uu____3739
                                                                   with
                                                                   | 
                                                                   (_msg,env,_uvar,term,typ,uu____3767)
                                                                    ->
                                                                    let uu____3768
                                                                    =
                                                                    FStar_Syntax_Util.head_and_args
                                                                    term  in
                                                                    (match uu____3768
                                                                    with
                                                                    | 
                                                                    (hd1,uu____3794)
                                                                    ->
                                                                    let uu____3815
                                                                    =
                                                                    let uu____3816
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    hd1  in
                                                                    uu____3816.FStar_Syntax_Syntax.n
                                                                     in
                                                                    (match uu____3815
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Tm_uvar
                                                                    uu____3829
                                                                    ->
                                                                    let uu____3846
                                                                    =
                                                                    let uu____3855
                                                                    =
                                                                    let uu____3858
                                                                    =
                                                                    let uu___86_3859
                                                                    = goal
                                                                     in
                                                                    let uu____3860
                                                                    =
                                                                    bnorm
                                                                    goal.FStar_Tactics_Types.context
                                                                    term  in
                                                                    let uu____3861
                                                                    =
                                                                    bnorm
                                                                    goal.FStar_Tactics_Types.context
                                                                    typ  in
                                                                    {
                                                                    FStar_Tactics_Types.context
                                                                    =
                                                                    (uu___86_3859.FStar_Tactics_Types.context);
                                                                    FStar_Tactics_Types.witness
                                                                    =
                                                                    uu____3860;
                                                                    FStar_Tactics_Types.goal_ty
                                                                    =
                                                                    uu____3861;
                                                                    FStar_Tactics_Types.opts
                                                                    =
                                                                    (uu___86_3859.FStar_Tactics_Types.opts);
                                                                    FStar_Tactics_Types.is_guard
                                                                    =
                                                                    (uu___86_3859.FStar_Tactics_Types.is_guard)
                                                                    }  in
                                                                    [uu____3858]
                                                                     in
                                                                    (uu____3855,
                                                                    [])  in
                                                                    ret
                                                                    uu____3846
                                                                    | 
                                                                    uu____3874
                                                                    ->
                                                                    let g_typ
                                                                    =
                                                                    let uu____3876
                                                                    =
                                                                    FStar_Options.__temp_fast_implicits
                                                                    ()  in
                                                                    if
                                                                    uu____3876
                                                                    then
                                                                    FStar_TypeChecker_TcTerm.check_type_of_well_typed_term
                                                                    false env
                                                                    term typ
                                                                    else
                                                                    (let term1
                                                                    =
                                                                    bnorm env
                                                                    term  in
                                                                    let uu____3879
                                                                    =
                                                                    let uu____3886
                                                                    =
                                                                    FStar_TypeChecker_Env.set_expected_typ
                                                                    env typ
                                                                     in
                                                                    env.FStar_TypeChecker_Env.type_of
                                                                    uu____3886
                                                                    term1  in
                                                                    match uu____3879
                                                                    with
                                                                    | 
                                                                    (uu____3887,uu____3888,g_typ)
                                                                    -> g_typ)
                                                                     in
                                                                    let uu____3890
                                                                    =
                                                                    goal_from_guard
                                                                    "apply_lemma solved arg"
                                                                    goal.FStar_Tactics_Types.context
                                                                    g_typ
                                                                    goal.FStar_Tactics_Types.opts
                                                                     in
                                                                    bind
                                                                    uu____3890
                                                                    (fun
                                                                    uu___58_3906
                                                                     ->
                                                                    match uu___58_3906
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
                                                         bind uu____3667
                                                           (fun goals_  ->
                                                              let sub_goals =
                                                                let uu____3974
                                                                  =
                                                                  FStar_List.map
                                                                    FStar_Pervasives_Native.fst
                                                                    goals_
                                                                   in
                                                                FStar_List.flatten
                                                                  uu____3974
                                                                 in
                                                              let smt_goals =
                                                                let uu____3996
                                                                  =
                                                                  FStar_List.map
                                                                    FStar_Pervasives_Native.snd
                                                                    goals_
                                                                   in
                                                                FStar_List.flatten
                                                                  uu____3996
                                                                 in
                                                              let rec filter'
                                                                a f xs =
                                                                match xs with
                                                                | [] -> []
                                                                | x::xs1 ->
                                                                    let uu____4051
                                                                    = f x xs1
                                                                     in
                                                                    if
                                                                    uu____4051
                                                                    then
                                                                    let uu____4054
                                                                    =
                                                                    filter'
                                                                    () f xs1
                                                                     in x ::
                                                                    uu____4054
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
                                                                    let uu____4068
                                                                    =
                                                                    checkone
                                                                    g.FStar_Tactics_Types.witness
                                                                    goals  in
                                                                    Prims.op_Negation
                                                                    uu____4068))
                                                                    a438 a439)
                                                                    (Obj.magic
                                                                    sub_goals))
                                                                 in
                                                              let uu____4069
                                                                =
                                                                add_goal_from_guard
                                                                  "apply_lemma guard"
                                                                  goal.FStar_Tactics_Types.context
                                                                  guard
                                                                  goal.FStar_Tactics_Types.opts
                                                                 in
                                                              bind uu____4069
                                                                (fun
                                                                   uu____4074
                                                                    ->
                                                                   let uu____4075
                                                                    =
                                                                    let uu____4078
                                                                    =
                                                                    let uu____4079
                                                                    =
                                                                    let uu____4080
                                                                    =
                                                                    FStar_Syntax_Util.mk_squash
                                                                    FStar_Syntax_Syntax.U_zero
                                                                    pre  in
                                                                    istrivial
                                                                    goal.FStar_Tactics_Types.context
                                                                    uu____4080
                                                                     in
                                                                    Prims.op_Negation
                                                                    uu____4079
                                                                     in
                                                                    if
                                                                    uu____4078
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
                                                                    uu____4075
                                                                    (fun
                                                                    uu____4086
                                                                     ->
                                                                    let uu____4087
                                                                    =
                                                                    add_smt_goals
                                                                    smt_goals
                                                                     in
                                                                    bind
                                                                    uu____4087
                                                                    (fun
                                                                    uu____4091
                                                                     ->
                                                                    add_goals
                                                                    sub_goals1)))))))))))))
         in
      focus uu____3019  in
    FStar_All.pipe_left (wrap_err "apply_lemma") uu____3016
  
let (destruct_eq' :
  FStar_Syntax_Syntax.typ ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun typ  ->
    let uu____4111 = FStar_Syntax_Util.destruct_typ_as_formula typ  in
    match uu____4111 with
    | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn
        (l,uu____4121::(e1,uu____4123)::(e2,uu____4125)::[])) when
        FStar_Ident.lid_equals l FStar_Parser_Const.eq2_lid ->
        FStar_Pervasives_Native.Some (e1, e2)
    | uu____4184 -> FStar_Pervasives_Native.None
  
let (destruct_eq :
  FStar_Syntax_Syntax.typ ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun typ  ->
    let uu____4206 = destruct_eq' typ  in
    match uu____4206 with
    | FStar_Pervasives_Native.Some t -> FStar_Pervasives_Native.Some t
    | FStar_Pervasives_Native.None  ->
        let uu____4236 = FStar_Syntax_Util.un_squash typ  in
        (match uu____4236 with
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
        let uu____4292 = FStar_TypeChecker_Env.pop_bv e1  in
        match uu____4292 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (bv',e') ->
            if FStar_Syntax_Syntax.bv_eq bvar bv'
            then FStar_Pervasives_Native.Some (e', [])
            else
              (let uu____4340 = aux e'  in
               FStar_Util.map_opt uu____4340
                 (fun uu____4364  ->
                    match uu____4364 with | (e'',bvs) -> (e'', (bv' :: bvs))))
         in
      let uu____4385 = aux e  in
      FStar_Util.map_opt uu____4385
        (fun uu____4409  ->
           match uu____4409 with | (e',bvs) -> (e', (FStar_List.rev bvs)))
  
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
          let uu____4464 = split_env b1 g.FStar_Tactics_Types.context  in
          FStar_Util.map_opt uu____4464
            (fun uu____4488  ->
               match uu____4488 with
               | (e0,bvs) ->
                   let s1 bv =
                     let uu___87_4505 = bv  in
                     let uu____4506 =
                       FStar_Syntax_Subst.subst s bv.FStar_Syntax_Syntax.sort
                        in
                     {
                       FStar_Syntax_Syntax.ppname =
                         (uu___87_4505.FStar_Syntax_Syntax.ppname);
                       FStar_Syntax_Syntax.index =
                         (uu___87_4505.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort = uu____4506
                     }  in
                   let bvs1 = FStar_List.map s1 bvs  in
                   let c = push_bvs e0 (b2 :: bvs1)  in
                   let w =
                     FStar_Syntax_Subst.subst s g.FStar_Tactics_Types.witness
                      in
                   let t =
                     FStar_Syntax_Subst.subst s g.FStar_Tactics_Types.goal_ty
                      in
                   let uu___88_4515 = g  in
                   {
                     FStar_Tactics_Types.context = c;
                     FStar_Tactics_Types.witness = w;
                     FStar_Tactics_Types.goal_ty = t;
                     FStar_Tactics_Types.opts =
                       (uu___88_4515.FStar_Tactics_Types.opts);
                     FStar_Tactics_Types.is_guard =
                       (uu___88_4515.FStar_Tactics_Types.is_guard)
                   })
  
let (rewrite : FStar_Syntax_Syntax.binder -> Prims.unit tac) =
  fun h  ->
    bind cur_goal
      (fun goal  ->
         let uu____4528 = h  in
         match uu____4528 with
         | (bv,uu____4532) ->
             mlog
               (fun uu____4536  ->
                  let uu____4537 = FStar_Syntax_Print.bv_to_string bv  in
                  let uu____4538 =
                    tts goal.FStar_Tactics_Types.context
                      bv.FStar_Syntax_Syntax.sort
                     in
                  FStar_Util.print2 "+++Rewrite %s : %s\n" uu____4537
                    uu____4538)
               (fun uu____4541  ->
                  let uu____4542 =
                    split_env bv goal.FStar_Tactics_Types.context  in
                  match uu____4542 with
                  | FStar_Pervasives_Native.None  ->
                      fail "rewrite: binder not found in environment"
                  | FStar_Pervasives_Native.Some (e0,bvs) ->
                      let uu____4571 =
                        destruct_eq bv.FStar_Syntax_Syntax.sort  in
                      (match uu____4571 with
                       | FStar_Pervasives_Native.Some (x,e) ->
                           let uu____4586 =
                             let uu____4587 = FStar_Syntax_Subst.compress x
                                in
                             uu____4587.FStar_Syntax_Syntax.n  in
                           (match uu____4586 with
                            | FStar_Syntax_Syntax.Tm_name x1 ->
                                let s = [FStar_Syntax_Syntax.NT (x1, e)]  in
                                let s1 bv1 =
                                  let uu___89_4600 = bv1  in
                                  let uu____4601 =
                                    FStar_Syntax_Subst.subst s
                                      bv1.FStar_Syntax_Syntax.sort
                                     in
                                  {
                                    FStar_Syntax_Syntax.ppname =
                                      (uu___89_4600.FStar_Syntax_Syntax.ppname);
                                    FStar_Syntax_Syntax.index =
                                      (uu___89_4600.FStar_Syntax_Syntax.index);
                                    FStar_Syntax_Syntax.sort = uu____4601
                                  }  in
                                let bvs1 = FStar_List.map s1 bvs  in
                                let uu____4607 =
                                  let uu___90_4608 = goal  in
                                  let uu____4609 = push_bvs e0 (bv :: bvs1)
                                     in
                                  let uu____4610 =
                                    FStar_Syntax_Subst.subst s
                                      goal.FStar_Tactics_Types.witness
                                     in
                                  let uu____4611 =
                                    FStar_Syntax_Subst.subst s
                                      goal.FStar_Tactics_Types.goal_ty
                                     in
                                  {
                                    FStar_Tactics_Types.context = uu____4609;
                                    FStar_Tactics_Types.witness = uu____4610;
                                    FStar_Tactics_Types.goal_ty = uu____4611;
                                    FStar_Tactics_Types.opts =
                                      (uu___90_4608.FStar_Tactics_Types.opts);
                                    FStar_Tactics_Types.is_guard =
                                      (uu___90_4608.FStar_Tactics_Types.is_guard)
                                  }  in
                                replace_cur uu____4607
                            | uu____4612 ->
                                fail
                                  "rewrite: Not an equality hypothesis with a variable on the LHS")
                       | uu____4613 ->
                           fail "rewrite: Not an equality hypothesis")))
  
let (rename_to :
  FStar_Syntax_Syntax.binder -> Prims.string -> Prims.unit tac) =
  fun b  ->
    fun s  ->
      bind cur_goal
        (fun goal  ->
           let uu____4638 = b  in
           match uu____4638 with
           | (bv,uu____4642) ->
               let bv' =
                 FStar_Syntax_Syntax.freshen_bv
                   (let uu___91_4646 = bv  in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (FStar_Ident.mk_ident
                           (s,
                             ((bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange)));
                      FStar_Syntax_Syntax.index =
                        (uu___91_4646.FStar_Syntax_Syntax.index);
                      FStar_Syntax_Syntax.sort =
                        (uu___91_4646.FStar_Syntax_Syntax.sort)
                    })
                  in
               let s1 =
                 let uu____4650 =
                   let uu____4651 =
                     let uu____4658 = FStar_Syntax_Syntax.bv_to_name bv'  in
                     (bv, uu____4658)  in
                   FStar_Syntax_Syntax.NT uu____4651  in
                 [uu____4650]  in
               let uu____4659 = subst_goal bv bv' s1 goal  in
               (match uu____4659 with
                | FStar_Pervasives_Native.None  ->
                    fail "rename_to: binder not found in environment"
                | FStar_Pervasives_Native.Some goal1 -> replace_cur goal1))
  
let (binder_retype : FStar_Syntax_Syntax.binder -> Prims.unit tac) =
  fun b  ->
    bind cur_goal
      (fun goal  ->
         let uu____4678 = b  in
         match uu____4678 with
         | (bv,uu____4682) ->
             let uu____4683 = split_env bv goal.FStar_Tactics_Types.context
                in
             (match uu____4683 with
              | FStar_Pervasives_Native.None  ->
                  fail "binder_retype: binder is not present in environment"
              | FStar_Pervasives_Native.Some (e0,bvs) ->
                  let uu____4712 = FStar_Syntax_Util.type_u ()  in
                  (match uu____4712 with
                   | (ty,u) ->
                       let uu____4721 = new_uvar "binder_retype" e0 ty  in
                       bind uu____4721
                         (fun t'  ->
                            let bv'' =
                              let uu___92_4731 = bv  in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___92_4731.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___92_4731.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = t'
                              }  in
                            let s =
                              let uu____4735 =
                                let uu____4736 =
                                  let uu____4743 =
                                    FStar_Syntax_Syntax.bv_to_name bv''  in
                                  (bv, uu____4743)  in
                                FStar_Syntax_Syntax.NT uu____4736  in
                              [uu____4735]  in
                            let bvs1 =
                              FStar_List.map
                                (fun b1  ->
                                   let uu___93_4751 = b1  in
                                   let uu____4752 =
                                     FStar_Syntax_Subst.subst s
                                       b1.FStar_Syntax_Syntax.sort
                                      in
                                   {
                                     FStar_Syntax_Syntax.ppname =
                                       (uu___93_4751.FStar_Syntax_Syntax.ppname);
                                     FStar_Syntax_Syntax.index =
                                       (uu___93_4751.FStar_Syntax_Syntax.index);
                                     FStar_Syntax_Syntax.sort = uu____4752
                                   }) bvs
                               in
                            let env' = push_bvs e0 (bv'' :: bvs1)  in
                            bind dismiss
                              (fun uu____4758  ->
                                 let uu____4759 =
                                   let uu____4762 =
                                     let uu____4765 =
                                       let uu___94_4766 = goal  in
                                       let uu____4767 =
                                         FStar_Syntax_Subst.subst s
                                           goal.FStar_Tactics_Types.witness
                                          in
                                       let uu____4768 =
                                         FStar_Syntax_Subst.subst s
                                           goal.FStar_Tactics_Types.goal_ty
                                          in
                                       {
                                         FStar_Tactics_Types.context = env';
                                         FStar_Tactics_Types.witness =
                                           uu____4767;
                                         FStar_Tactics_Types.goal_ty =
                                           uu____4768;
                                         FStar_Tactics_Types.opts =
                                           (uu___94_4766.FStar_Tactics_Types.opts);
                                         FStar_Tactics_Types.is_guard =
                                           (uu___94_4766.FStar_Tactics_Types.is_guard)
                                       }  in
                                     [uu____4765]  in
                                   add_goals uu____4762  in
                                 bind uu____4759
                                   (fun uu____4771  ->
                                      let uu____4772 =
                                        FStar_Syntax_Util.mk_eq2
                                          (FStar_Syntax_Syntax.U_succ u) ty
                                          bv.FStar_Syntax_Syntax.sort t'
                                         in
                                      add_irrelevant_goal
                                        "binder_retype equation" e0
                                        uu____4772
                                        goal.FStar_Tactics_Types.opts))))))
  
let (norm_binder_type :
  FStar_Syntax_Embeddings.norm_step Prims.list ->
    FStar_Syntax_Syntax.binder -> Prims.unit tac)
  =
  fun s  ->
    fun b  ->
      bind cur_goal
        (fun goal  ->
           let uu____4793 = b  in
           match uu____4793 with
           | (bv,uu____4797) ->
               let uu____4798 = split_env bv goal.FStar_Tactics_Types.context
                  in
               (match uu____4798 with
                | FStar_Pervasives_Native.None  ->
                    fail
                      "binder_retype: binder is not present in environment"
                | FStar_Pervasives_Native.Some (e0,bvs) ->
                    let steps =
                      let uu____4830 =
                        FStar_TypeChecker_Normalize.tr_norm_steps s  in
                      FStar_List.append
                        [FStar_TypeChecker_Normalize.Reify;
                        FStar_TypeChecker_Normalize.UnfoldTac] uu____4830
                       in
                    let sort' =
                      normalize steps e0 bv.FStar_Syntax_Syntax.sort  in
                    let bv' =
                      let uu___95_4835 = bv  in
                      {
                        FStar_Syntax_Syntax.ppname =
                          (uu___95_4835.FStar_Syntax_Syntax.ppname);
                        FStar_Syntax_Syntax.index =
                          (uu___95_4835.FStar_Syntax_Syntax.index);
                        FStar_Syntax_Syntax.sort = sort'
                      }  in
                    let env' = push_bvs e0 (bv' :: bvs)  in
                    replace_cur
                      (let uu___96_4839 = goal  in
                       {
                         FStar_Tactics_Types.context = env';
                         FStar_Tactics_Types.witness =
                           (uu___96_4839.FStar_Tactics_Types.witness);
                         FStar_Tactics_Types.goal_ty =
                           (uu___96_4839.FStar_Tactics_Types.goal_ty);
                         FStar_Tactics_Types.opts =
                           (uu___96_4839.FStar_Tactics_Types.opts);
                         FStar_Tactics_Types.is_guard =
                           (uu___96_4839.FStar_Tactics_Types.is_guard)
                       })))
  
let (revert : Prims.unit tac) =
  bind cur_goal
    (fun goal  ->
       let uu____4847 =
         FStar_TypeChecker_Env.pop_bv goal.FStar_Tactics_Types.context  in
       match uu____4847 with
       | FStar_Pervasives_Native.None  -> fail "Cannot revert; empty context"
       | FStar_Pervasives_Native.Some (x,env') ->
           let typ' =
             let uu____4869 =
               FStar_Syntax_Syntax.mk_Total goal.FStar_Tactics_Types.goal_ty
                in
             FStar_Syntax_Util.arrow [(x, FStar_Pervasives_Native.None)]
               uu____4869
              in
           let w' =
             FStar_Syntax_Util.abs [(x, FStar_Pervasives_Native.None)]
               goal.FStar_Tactics_Types.witness FStar_Pervasives_Native.None
              in
           replace_cur
             (let uu___97_4903 = goal  in
              {
                FStar_Tactics_Types.context = env';
                FStar_Tactics_Types.witness = w';
                FStar_Tactics_Types.goal_ty = typ';
                FStar_Tactics_Types.opts =
                  (uu___97_4903.FStar_Tactics_Types.opts);
                FStar_Tactics_Types.is_guard =
                  (uu___97_4903.FStar_Tactics_Types.is_guard)
              }))
  
let (free_in :
  FStar_Syntax_Syntax.bv -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun bv  ->
    fun t  ->
      let uu____4910 = FStar_Syntax_Free.names t  in
      FStar_Util.set_mem bv uu____4910
  
let rec (clear : FStar_Syntax_Syntax.binder -> Prims.unit tac) =
  fun b  ->
    let bv = FStar_Pervasives_Native.fst b  in
    bind cur_goal
      (fun goal  ->
         mlog
           (fun uu____4926  ->
              let uu____4927 = FStar_Syntax_Print.binder_to_string b  in
              let uu____4928 =
                let uu____4929 =
                  let uu____4930 =
                    FStar_TypeChecker_Env.all_binders
                      goal.FStar_Tactics_Types.context
                     in
                  FStar_All.pipe_right uu____4930 FStar_List.length  in
                FStar_All.pipe_right uu____4929 FStar_Util.string_of_int  in
              FStar_Util.print2 "Clear of (%s), env has %s binders\n"
                uu____4927 uu____4928)
           (fun uu____4941  ->
              let uu____4942 = split_env bv goal.FStar_Tactics_Types.context
                 in
              match uu____4942 with
              | FStar_Pervasives_Native.None  ->
                  fail "Cannot clear; binder not in environment"
              | FStar_Pervasives_Native.Some (e',bvs) ->
                  let rec check bvs1 =
                    match bvs1 with
                    | [] -> ret ()
                    | bv'::bvs2 ->
                        let uu____4987 =
                          free_in bv bv'.FStar_Syntax_Syntax.sort  in
                        if uu____4987
                        then
                          let uu____4990 =
                            let uu____4991 =
                              FStar_Syntax_Print.bv_to_string bv'  in
                            FStar_Util.format1
                              "Cannot clear; binder present in the type of %s"
                              uu____4991
                             in
                          fail uu____4990
                        else check bvs2
                     in
                  let uu____4993 =
                    free_in bv goal.FStar_Tactics_Types.goal_ty  in
                  if uu____4993
                  then fail "Cannot clear; binder present in goal"
                  else
                    (let uu____4997 = check bvs  in
                     bind uu____4997
                       (fun uu____5003  ->
                          let env' = push_bvs e' bvs  in
                          let uu____5005 =
                            new_uvar "clear.witness" env'
                              goal.FStar_Tactics_Types.goal_ty
                             in
                          bind uu____5005
                            (fun ut  ->
                               let uu____5011 =
                                 do_unify goal.FStar_Tactics_Types.context
                                   goal.FStar_Tactics_Types.witness ut
                                  in
                               if uu____5011
                               then
                                 replace_cur
                                   (let uu___98_5016 = goal  in
                                    {
                                      FStar_Tactics_Types.context = env';
                                      FStar_Tactics_Types.witness = ut;
                                      FStar_Tactics_Types.goal_ty =
                                        (uu___98_5016.FStar_Tactics_Types.goal_ty);
                                      FStar_Tactics_Types.opts =
                                        (uu___98_5016.FStar_Tactics_Types.opts);
                                      FStar_Tactics_Types.is_guard =
                                        (uu___98_5016.FStar_Tactics_Types.is_guard)
                                    })
                               else
                                 fail
                                   "Cannot clear; binder appears in witness")))))
  
let (clear_top : Prims.unit tac) =
  bind cur_goal
    (fun goal  ->
       let uu____5025 =
         FStar_TypeChecker_Env.pop_bv goal.FStar_Tactics_Types.context  in
       match uu____5025 with
       | FStar_Pervasives_Native.None  -> fail "Cannot clear; empty context"
       | FStar_Pervasives_Native.Some (x,uu____5039) ->
           let uu____5044 = FStar_Syntax_Syntax.mk_binder x  in
           clear uu____5044)
  
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
           let uu___99_5060 = g  in
           {
             FStar_Tactics_Types.context = ctx';
             FStar_Tactics_Types.witness =
               (uu___99_5060.FStar_Tactics_Types.witness);
             FStar_Tactics_Types.goal_ty =
               (uu___99_5060.FStar_Tactics_Types.goal_ty);
             FStar_Tactics_Types.opts =
               (uu___99_5060.FStar_Tactics_Types.opts);
             FStar_Tactics_Types.is_guard =
               (uu___99_5060.FStar_Tactics_Types.is_guard)
           }  in
         bind dismiss (fun uu____5062  -> add_goals [g']))
  
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
           let uu___100_5078 = g  in
           {
             FStar_Tactics_Types.context = ctx';
             FStar_Tactics_Types.witness =
               (uu___100_5078.FStar_Tactics_Types.witness);
             FStar_Tactics_Types.goal_ty =
               (uu___100_5078.FStar_Tactics_Types.goal_ty);
             FStar_Tactics_Types.opts =
               (uu___100_5078.FStar_Tactics_Types.opts);
             FStar_Tactics_Types.is_guard =
               (uu___100_5078.FStar_Tactics_Types.is_guard)
           }  in
         bind dismiss (fun uu____5080  -> add_goals [g']))
  
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
            let uu____5112 = FStar_Syntax_Subst.compress t  in
            uu____5112.FStar_Syntax_Syntax.n  in
          let uu____5115 =
            if d = FStar_Tactics_Types.TopDown
            then
              f env
                (let uu___102_5121 = t  in
                 {
                   FStar_Syntax_Syntax.n = tn;
                   FStar_Syntax_Syntax.pos =
                     (uu___102_5121.FStar_Syntax_Syntax.pos);
                   FStar_Syntax_Syntax.vars =
                     (uu___102_5121.FStar_Syntax_Syntax.vars)
                 })
            else ret t  in
          bind uu____5115
            (fun t1  ->
               let tn1 =
                 let uu____5129 =
                   let uu____5130 = FStar_Syntax_Subst.compress t1  in
                   uu____5130.FStar_Syntax_Syntax.n  in
                 match uu____5129 with
                 | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
                     let ff = tac_fold_env d f env  in
                     let uu____5162 = ff hd1  in
                     bind uu____5162
                       (fun hd2  ->
                          let fa uu____5182 =
                            match uu____5182 with
                            | (a,q) ->
                                let uu____5195 = ff a  in
                                bind uu____5195 (fun a1  -> ret (a1, q))
                             in
                          let uu____5208 = mapM fa args  in
                          bind uu____5208
                            (fun args1  ->
                               ret (FStar_Syntax_Syntax.Tm_app (hd2, args1))))
                 | FStar_Syntax_Syntax.Tm_abs (bs,t2,k) ->
                     let uu____5268 = FStar_Syntax_Subst.open_term bs t2  in
                     (match uu____5268 with
                      | (bs1,t') ->
                          let uu____5277 =
                            let uu____5280 =
                              FStar_TypeChecker_Env.push_binders env bs1  in
                            tac_fold_env d f uu____5280 t'  in
                          bind uu____5277
                            (fun t''  ->
                               let uu____5284 =
                                 let uu____5285 =
                                   let uu____5302 =
                                     FStar_Syntax_Subst.close_binders bs1  in
                                   let uu____5303 =
                                     FStar_Syntax_Subst.close bs1 t''  in
                                   (uu____5302, uu____5303, k)  in
                                 FStar_Syntax_Syntax.Tm_abs uu____5285  in
                               ret uu____5284))
                 | FStar_Syntax_Syntax.Tm_arrow (bs,k) -> ret tn
                 | uu____5324 -> ret tn  in
               bind tn1
                 (fun tn2  ->
                    let t' =
                      let uu___101_5331 = t1  in
                      {
                        FStar_Syntax_Syntax.n = tn2;
                        FStar_Syntax_Syntax.pos =
                          (uu___101_5331.FStar_Syntax_Syntax.pos);
                        FStar_Syntax_Syntax.vars =
                          (uu___101_5331.FStar_Syntax_Syntax.vars)
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
            let uu____5360 = FStar_TypeChecker_TcTerm.tc_term env t  in
            match uu____5360 with
            | (t1,lcomp,g) ->
                let uu____5372 =
                  (let uu____5375 =
                     FStar_Syntax_Util.is_pure_or_ghost_lcomp lcomp  in
                   Prims.op_Negation uu____5375) ||
                    (let uu____5377 = FStar_TypeChecker_Rel.is_trivial g  in
                     Prims.op_Negation uu____5377)
                   in
                if uu____5372
                then ret t1
                else
                  (let rewrite_eq =
                     let typ = lcomp.FStar_Syntax_Syntax.res_typ  in
                     let uu____5387 = new_uvar "pointwise_rec" env typ  in
                     bind uu____5387
                       (fun ut  ->
                          log ps
                            (fun uu____5398  ->
                               let uu____5399 =
                                 FStar_Syntax_Print.term_to_string t1  in
                               let uu____5400 =
                                 FStar_Syntax_Print.term_to_string ut  in
                               FStar_Util.print2
                                 "Pointwise_rec: making equality\n\t%s ==\n\t%s\n"
                                 uu____5399 uu____5400);
                          (let uu____5401 =
                             let uu____5404 =
                               let uu____5405 =
                                 FStar_TypeChecker_TcTerm.universe_of env typ
                                  in
                               FStar_Syntax_Util.mk_eq2 uu____5405 typ t1 ut
                                in
                             add_irrelevant_goal "pointwise_rec equation" env
                               uu____5404 opts
                              in
                           bind uu____5401
                             (fun uu____5408  ->
                                let uu____5409 =
                                  bind tau
                                    (fun uu____5415  ->
                                       let ut1 =
                                         FStar_TypeChecker_Normalize.reduce_uvar_solutions
                                           env ut
                                          in
                                       log ps
                                         (fun uu____5421  ->
                                            let uu____5422 =
                                              FStar_Syntax_Print.term_to_string
                                                t1
                                               in
                                            let uu____5423 =
                                              FStar_Syntax_Print.term_to_string
                                                ut1
                                               in
                                            FStar_Util.print2
                                              "Pointwise_rec: succeeded rewriting\n\t%s to\n\t%s\n"
                                              uu____5422 uu____5423);
                                       ret ut1)
                                   in
                                focus uu____5409)))
                      in
                   let uu____5424 = trytac' rewrite_eq  in
                   bind uu____5424
                     (fun x  ->
                        match x with
                        | FStar_Util.Inl "SKIP" -> ret t1
                        | FStar_Util.Inl e -> fail e
                        | FStar_Util.Inr x1 -> ret x1))
  
let (pointwise :
  FStar_Tactics_Types.direction -> Prims.unit tac -> Prims.unit tac) =
  fun d  ->
    fun tau  ->
      bind get
        (fun ps  ->
           let uu____5466 =
             match ps.FStar_Tactics_Types.goals with
             | g::gs -> (g, gs)
             | [] -> failwith "Pointwise: no goals"  in
           match uu____5466 with
           | (g,gs) ->
               let gt1 = g.FStar_Tactics_Types.goal_ty  in
               (log ps
                  (fun uu____5503  ->
                     let uu____5504 = FStar_Syntax_Print.term_to_string gt1
                        in
                     FStar_Util.print1 "Pointwise starting with %s\n"
                       uu____5504);
                bind dismiss_all
                  (fun uu____5507  ->
                     let uu____5508 =
                       tac_fold_env d
                         (pointwise_rec ps tau g.FStar_Tactics_Types.opts)
                         g.FStar_Tactics_Types.context gt1
                        in
                     bind uu____5508
                       (fun gt'  ->
                          log ps
                            (fun uu____5518  ->
                               let uu____5519 =
                                 FStar_Syntax_Print.term_to_string gt'  in
                               FStar_Util.print1
                                 "Pointwise seems to have succeded with %s\n"
                                 uu____5519);
                          (let uu____5520 = push_goals gs  in
                           bind uu____5520
                             (fun uu____5524  ->
                                add_goals
                                  [(let uu___103_5526 = g  in
                                    {
                                      FStar_Tactics_Types.context =
                                        (uu___103_5526.FStar_Tactics_Types.context);
                                      FStar_Tactics_Types.witness =
                                        (uu___103_5526.FStar_Tactics_Types.witness);
                                      FStar_Tactics_Types.goal_ty = gt';
                                      FStar_Tactics_Types.opts =
                                        (uu___103_5526.FStar_Tactics_Types.opts);
                                      FStar_Tactics_Types.is_guard =
                                        (uu___103_5526.FStar_Tactics_Types.is_guard)
                                    })]))))))
  
let (trefl : Prims.unit tac) =
  bind cur_goal
    (fun g  ->
       let uu____5548 =
         FStar_Syntax_Util.un_squash g.FStar_Tactics_Types.goal_ty  in
       match uu____5548 with
       | FStar_Pervasives_Native.Some t ->
           let uu____5560 = FStar_Syntax_Util.head_and_args' t  in
           (match uu____5560 with
            | (hd1,args) ->
                let uu____5593 =
                  let uu____5606 =
                    let uu____5607 = FStar_Syntax_Util.un_uinst hd1  in
                    uu____5607.FStar_Syntax_Syntax.n  in
                  (uu____5606, args)  in
                (match uu____5593 with
                 | (FStar_Syntax_Syntax.Tm_fvar
                    fv,uu____5621::(l,uu____5623)::(r,uu____5625)::[]) when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.eq2_lid
                     ->
                     let uu____5672 =
                       let uu____5673 =
                         do_unify g.FStar_Tactics_Types.context l r  in
                       Prims.op_Negation uu____5673  in
                     if uu____5672
                     then
                       let uu____5676 = tts g.FStar_Tactics_Types.context l
                          in
                       let uu____5677 = tts g.FStar_Tactics_Types.context r
                          in
                       fail2 "trefl: not a trivial equality (%s vs %s)"
                         uu____5676 uu____5677
                     else solve g FStar_Syntax_Util.exp_unit
                 | (hd2,uu____5680) ->
                     let uu____5697 = tts g.FStar_Tactics_Types.context t  in
                     fail1 "trefl: not an equality (%s)" uu____5697))
       | FStar_Pervasives_Native.None  -> fail "not an irrelevant goal")
  
let (dup : Prims.unit tac) =
  bind cur_goal
    (fun g  ->
       let uu____5707 =
         new_uvar "dup" g.FStar_Tactics_Types.context
           g.FStar_Tactics_Types.goal_ty
          in
       bind uu____5707
         (fun u  ->
            let g' =
              let uu___104_5714 = g  in
              {
                FStar_Tactics_Types.context =
                  (uu___104_5714.FStar_Tactics_Types.context);
                FStar_Tactics_Types.witness = u;
                FStar_Tactics_Types.goal_ty =
                  (uu___104_5714.FStar_Tactics_Types.goal_ty);
                FStar_Tactics_Types.opts =
                  (uu___104_5714.FStar_Tactics_Types.opts);
                FStar_Tactics_Types.is_guard =
                  (uu___104_5714.FStar_Tactics_Types.is_guard)
              }  in
            bind dismiss
              (fun uu____5717  ->
                 let uu____5718 =
                   let uu____5721 =
                     let uu____5722 =
                       FStar_TypeChecker_TcTerm.universe_of
                         g.FStar_Tactics_Types.context
                         g.FStar_Tactics_Types.goal_ty
                        in
                     FStar_Syntax_Util.mk_eq2 uu____5722
                       g.FStar_Tactics_Types.goal_ty u
                       g.FStar_Tactics_Types.witness
                      in
                   add_irrelevant_goal "dup equation"
                     g.FStar_Tactics_Types.context uu____5721
                     g.FStar_Tactics_Types.opts
                    in
                 bind uu____5718
                   (fun uu____5725  ->
                      let uu____5726 = add_goals [g']  in
                      bind uu____5726 (fun uu____5730  -> ret ())))))
  
let (flip : Prims.unit tac) =
  bind get
    (fun ps  ->
       match ps.FStar_Tactics_Types.goals with
       | g1::g2::gs ->
           set
             (let uu___105_5749 = ps  in
              {
                FStar_Tactics_Types.main_context =
                  (uu___105_5749.FStar_Tactics_Types.main_context);
                FStar_Tactics_Types.main_goal =
                  (uu___105_5749.FStar_Tactics_Types.main_goal);
                FStar_Tactics_Types.all_implicits =
                  (uu___105_5749.FStar_Tactics_Types.all_implicits);
                FStar_Tactics_Types.goals = (g2 :: g1 :: gs);
                FStar_Tactics_Types.smt_goals =
                  (uu___105_5749.FStar_Tactics_Types.smt_goals);
                FStar_Tactics_Types.depth =
                  (uu___105_5749.FStar_Tactics_Types.depth);
                FStar_Tactics_Types.__dump =
                  (uu___105_5749.FStar_Tactics_Types.__dump);
                FStar_Tactics_Types.psc =
                  (uu___105_5749.FStar_Tactics_Types.psc);
                FStar_Tactics_Types.entry_range =
                  (uu___105_5749.FStar_Tactics_Types.entry_range)
              })
       | uu____5750 -> fail "flip: less than 2 goals")
  
let (later : Prims.unit tac) =
  bind get
    (fun ps  ->
       match ps.FStar_Tactics_Types.goals with
       | [] -> ret ()
       | g::gs ->
           set
             (let uu___106_5767 = ps  in
              {
                FStar_Tactics_Types.main_context =
                  (uu___106_5767.FStar_Tactics_Types.main_context);
                FStar_Tactics_Types.main_goal =
                  (uu___106_5767.FStar_Tactics_Types.main_goal);
                FStar_Tactics_Types.all_implicits =
                  (uu___106_5767.FStar_Tactics_Types.all_implicits);
                FStar_Tactics_Types.goals = (FStar_List.append gs [g]);
                FStar_Tactics_Types.smt_goals =
                  (uu___106_5767.FStar_Tactics_Types.smt_goals);
                FStar_Tactics_Types.depth =
                  (uu___106_5767.FStar_Tactics_Types.depth);
                FStar_Tactics_Types.__dump =
                  (uu___106_5767.FStar_Tactics_Types.__dump);
                FStar_Tactics_Types.psc =
                  (uu___106_5767.FStar_Tactics_Types.psc);
                FStar_Tactics_Types.entry_range =
                  (uu___106_5767.FStar_Tactics_Types.entry_range)
              }))
  
let (qed : Prims.unit tac) =
  bind get
    (fun ps  ->
       match ps.FStar_Tactics_Types.goals with
       | [] -> ret ()
       | uu____5776 -> fail "Not done!")
  
let (cases :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 tac)
  =
  fun t  ->
    let uu____5794 =
      bind cur_goal
        (fun g  ->
           let uu____5808 = __tc g.FStar_Tactics_Types.context t  in
           bind uu____5808
             (fun uu____5844  ->
                match uu____5844 with
                | (t1,typ,guard) ->
                    let uu____5860 = FStar_Syntax_Util.head_and_args typ  in
                    (match uu____5860 with
                     | (hd1,args) ->
                         let uu____5903 =
                           let uu____5916 =
                             let uu____5917 = FStar_Syntax_Util.un_uinst hd1
                                in
                             uu____5917.FStar_Syntax_Syntax.n  in
                           (uu____5916, args)  in
                         (match uu____5903 with
                          | (FStar_Syntax_Syntax.Tm_fvar
                             fv,(p,uu____5936)::(q,uu____5938)::[]) when
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
                                let uu___107_5976 = g  in
                                let uu____5977 =
                                  FStar_TypeChecker_Env.push_bv
                                    g.FStar_Tactics_Types.context v_p
                                   in
                                {
                                  FStar_Tactics_Types.context = uu____5977;
                                  FStar_Tactics_Types.witness =
                                    (uu___107_5976.FStar_Tactics_Types.witness);
                                  FStar_Tactics_Types.goal_ty =
                                    (uu___107_5976.FStar_Tactics_Types.goal_ty);
                                  FStar_Tactics_Types.opts =
                                    (uu___107_5976.FStar_Tactics_Types.opts);
                                  FStar_Tactics_Types.is_guard =
                                    (uu___107_5976.FStar_Tactics_Types.is_guard)
                                }  in
                              let g2 =
                                let uu___108_5979 = g  in
                                let uu____5980 =
                                  FStar_TypeChecker_Env.push_bv
                                    g.FStar_Tactics_Types.context v_q
                                   in
                                {
                                  FStar_Tactics_Types.context = uu____5980;
                                  FStar_Tactics_Types.witness =
                                    (uu___108_5979.FStar_Tactics_Types.witness);
                                  FStar_Tactics_Types.goal_ty =
                                    (uu___108_5979.FStar_Tactics_Types.goal_ty);
                                  FStar_Tactics_Types.opts =
                                    (uu___108_5979.FStar_Tactics_Types.opts);
                                  FStar_Tactics_Types.is_guard =
                                    (uu___108_5979.FStar_Tactics_Types.is_guard)
                                }  in
                              bind dismiss
                                (fun uu____5987  ->
                                   let uu____5988 = add_goals [g1; g2]  in
                                   bind uu____5988
                                     (fun uu____5997  ->
                                        let uu____5998 =
                                          let uu____6003 =
                                            FStar_Syntax_Syntax.bv_to_name
                                              v_p
                                             in
                                          let uu____6004 =
                                            FStar_Syntax_Syntax.bv_to_name
                                              v_q
                                             in
                                          (uu____6003, uu____6004)  in
                                        ret uu____5998))
                          | uu____6009 ->
                              let uu____6022 =
                                tts g.FStar_Tactics_Types.context typ  in
                              fail1 "Not a disjunction: %s" uu____6022))))
       in
    FStar_All.pipe_left (wrap_err "cases") uu____5794
  
let (set_options : Prims.string -> Prims.unit tac) =
  fun s  ->
    bind cur_goal
      (fun g  ->
         FStar_Options.push ();
         (let uu____6060 = FStar_Util.smap_copy g.FStar_Tactics_Types.opts
             in
          FStar_Options.set uu____6060);
         (let res = FStar_Options.set_options FStar_Options.Set s  in
          let opts' = FStar_Options.peek ()  in
          FStar_Options.pop ();
          (match res with
           | FStar_Getopt.Success  ->
               let g' =
                 let uu___109_6067 = g  in
                 {
                   FStar_Tactics_Types.context =
                     (uu___109_6067.FStar_Tactics_Types.context);
                   FStar_Tactics_Types.witness =
                     (uu___109_6067.FStar_Tactics_Types.witness);
                   FStar_Tactics_Types.goal_ty =
                     (uu___109_6067.FStar_Tactics_Types.goal_ty);
                   FStar_Tactics_Types.opts = opts';
                   FStar_Tactics_Types.is_guard =
                     (uu___109_6067.FStar_Tactics_Types.is_guard)
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
      let uu____6111 =
        bind cur_goal
          (fun goal  ->
             let env =
               FStar_TypeChecker_Env.set_expected_typ
                 goal.FStar_Tactics_Types.context ty
                in
             let uu____6119 = __tc env tm  in
             bind uu____6119
               (fun uu____6139  ->
                  match uu____6139 with
                  | (tm1,typ,guard) ->
                      (FStar_TypeChecker_Rel.force_trivial_guard env guard;
                       ret tm1)))
         in
      FStar_All.pipe_left (wrap_err "unquote") uu____6111
  
let (uvar_env :
  env ->
    FStar_Syntax_Syntax.typ FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.term tac)
  =
  fun env  ->
    fun ty  ->
      let uu____6170 =
        match ty with
        | FStar_Pervasives_Native.Some ty1 -> ret ty1
        | FStar_Pervasives_Native.None  ->
            let uu____6176 =
              let uu____6177 = FStar_Syntax_Util.type_u ()  in
              FStar_All.pipe_left FStar_Pervasives_Native.fst uu____6177  in
            new_uvar "uvar_env.2" env uu____6176
         in
      bind uu____6170
        (fun typ  ->
           let uu____6189 = new_uvar "uvar_env" env typ  in
           bind uu____6189 (fun t  -> ret t))
  
let (unshelve : FStar_Syntax_Syntax.term -> Prims.unit tac) =
  fun t  ->
    let uu____6201 =
      bind cur_goal
        (fun goal  ->
           let uu____6207 = __tc goal.FStar_Tactics_Types.context t  in
           bind uu____6207
             (fun uu____6227  ->
                match uu____6227 with
                | (t1,typ,guard) ->
                    let uu____6239 =
                      must_trivial goal.FStar_Tactics_Types.context guard  in
                    bind uu____6239
                      (fun uu____6244  ->
                         let uu____6245 =
                           let uu____6248 =
                             let uu___110_6249 = goal  in
                             let uu____6250 =
                               bnorm goal.FStar_Tactics_Types.context t1  in
                             let uu____6251 =
                               bnorm goal.FStar_Tactics_Types.context typ  in
                             {
                               FStar_Tactics_Types.context =
                                 (uu___110_6249.FStar_Tactics_Types.context);
                               FStar_Tactics_Types.witness = uu____6250;
                               FStar_Tactics_Types.goal_ty = uu____6251;
                               FStar_Tactics_Types.opts =
                                 (uu___110_6249.FStar_Tactics_Types.opts);
                               FStar_Tactics_Types.is_guard = false
                             }  in
                           [uu____6248]  in
                         add_goals uu____6245)))
       in
    FStar_All.pipe_left (wrap_err "unshelve") uu____6201
  
let (unify :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool tac) =
  fun t1  ->
    fun t2  ->
      bind get
        (fun ps  ->
           let uu____6269 =
             do_unify ps.FStar_Tactics_Types.main_context t1 t2  in
           ret uu____6269)
  
let (launch_process :
  Prims.string -> Prims.string -> Prims.string -> Prims.string tac) =
  fun prog  ->
    fun args  ->
      fun input  ->
        bind idtac
          (fun uu____6286  ->
             let uu____6287 = FStar_Options.unsafe_tactic_exec ()  in
             if uu____6287
             then
               let s =
                 FStar_Util.launch_process true "tactic_launch" prog args
                   input (fun uu____6293  -> fun uu____6294  -> false)
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
        (fun uu____6308  ->
           let uu____6309 =
             FStar_Syntax_Syntax.gen_bv nm FStar_Pervasives_Native.None t  in
           ret uu____6309)
  
let (goal_of_goal_ty :
  env ->
    FStar_Syntax_Syntax.typ ->
      (FStar_Tactics_Types.goal,FStar_TypeChecker_Env.guard_t)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun typ  ->
      let uu____6324 =
        FStar_TypeChecker_Util.new_implicit_var "proofstate_of_goal_ty"
          typ.FStar_Syntax_Syntax.pos env typ
         in
      match uu____6324 with
      | (u,uu____6342,g_u) ->
          let g =
            let uu____6357 = FStar_Options.peek ()  in
            {
              FStar_Tactics_Types.context = env;
              FStar_Tactics_Types.witness = u;
              FStar_Tactics_Types.goal_ty = typ;
              FStar_Tactics_Types.opts = uu____6357;
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
      let uu____6368 = goal_of_goal_ty env typ  in
      match uu____6368 with
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
  