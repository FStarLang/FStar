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
      FStar_All.pipe_right uu____310 FStar_Syntax_Print.binders_to_json  in
    let uu____311 =
      let uu____318 =
        let uu____325 =
          let uu____330 =
            let uu____331 =
              let uu____338 =
                let uu____343 =
                  let uu____344 =
                    tts g.FStar_Tactics_Types.context
                      g.FStar_Tactics_Types.witness
                     in
                  FStar_Util.JsonStr uu____344  in
                ("witness", uu____343)  in
              let uu____345 =
                let uu____352 =
                  let uu____357 =
                    let uu____358 =
                      tts g.FStar_Tactics_Types.context
                        g.FStar_Tactics_Types.goal_ty
                       in
                    FStar_Util.JsonStr uu____358  in
                  ("type", uu____357)  in
                [uu____352]  in
              uu____338 :: uu____345  in
            FStar_Util.JsonAssoc uu____331  in
          ("goal", uu____330)  in
        [uu____325]  in
      ("hyps", g_binders) :: uu____318  in
    FStar_Util.JsonAssoc uu____311
  
let (ps_to_json :
  (Prims.string,FStar_Tactics_Types.proofstate)
    FStar_Pervasives_Native.tuple2 -> FStar_Util.json)
  =
  fun uu____389  ->
    match uu____389 with
    | (msg,ps) ->
        let uu____396 =
          let uu____403 =
            let uu____410 =
              let uu____415 =
                let uu____416 =
                  FStar_List.map goal_to_json ps.FStar_Tactics_Types.goals
                   in
                FStar_Util.JsonList uu____416  in
              ("goals", uu____415)  in
            let uu____419 =
              let uu____426 =
                let uu____431 =
                  let uu____432 =
                    FStar_List.map goal_to_json
                      ps.FStar_Tactics_Types.smt_goals
                     in
                  FStar_Util.JsonList uu____432  in
                ("smt-goals", uu____431)  in
              [uu____426]  in
            uu____410 :: uu____419  in
          ("label", (FStar_Util.JsonStr msg)) :: uu____403  in
        FStar_Util.JsonAssoc uu____396
  
let (dump_proofstate :
  FStar_Tactics_Types.proofstate -> Prims.string -> Prims.unit) =
  fun ps  ->
    fun msg  ->
      FStar_Options.with_saved_options
        (fun uu____459  ->
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
         (let uu____480 = FStar_Tactics_Types.subst_proof_state subst1 ps  in
          dump_cur uu____480 msg);
         FStar_Tactics_Result.Success ((), ps))
  
let (print_proof_state : Prims.string -> Prims.unit tac) =
  fun msg  ->
    mk_tac
      (fun ps  ->
         let psc = ps.FStar_Tactics_Types.psc  in
         let subst1 = FStar_TypeChecker_Normalize.psc_subst psc  in
         (let uu____496 = FStar_Tactics_Types.subst_proof_state subst1 ps  in
          dump_proofstate uu____496 msg);
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
      let uu____557 = FStar_ST.op_Bang tac_verb_dbg  in
      match uu____557 with
      | FStar_Pervasives_Native.None  ->
          ((let uu____584 =
              let uu____587 =
                FStar_TypeChecker_Env.debug
                  ps.FStar_Tactics_Types.main_context
                  (FStar_Options.Other "TacVerbose")
                 in
              FStar_Pervasives_Native.Some uu____587  in
            FStar_ST.op_Colon_Equals tac_verb_dbg uu____584);
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
         (let uu____656 =
            FStar_TypeChecker_Env.debug ps.FStar_Tactics_Types.main_context
              (FStar_Options.Other "TacFail")
             in
          if uu____656
          then dump_proofstate ps (Prims.strcat "TACTING FAILING: " msg)
          else ());
         FStar_Tactics_Result.Failed (msg, ps))
  
let fail1 : 'Auu____661 . Prims.string -> Prims.string -> 'Auu____661 tac =
  fun msg  ->
    fun x  -> let uu____672 = FStar_Util.format1 msg x  in fail uu____672
  
let fail2 :
  'Auu____677 .
    Prims.string -> Prims.string -> Prims.string -> 'Auu____677 tac
  =
  fun msg  ->
    fun x  ->
      fun y  -> let uu____692 = FStar_Util.format2 msg x y  in fail uu____692
  
let fail3 :
  'Auu____698 .
    Prims.string ->
      Prims.string -> Prims.string -> Prims.string -> 'Auu____698 tac
  =
  fun msg  ->
    fun x  ->
      fun y  ->
        fun z  ->
          let uu____717 = FStar_Util.format3 msg x y z  in fail uu____717
  
let trytac' : 'a . 'a tac -> (Prims.string,'a) FStar_Util.either tac =
  fun t  ->
    mk_tac
      (fun ps  ->
         let tx = FStar_Syntax_Unionfind.new_transaction ()  in
         let uu____747 = run t ps  in
         match uu____747 with
         | FStar_Tactics_Result.Success (a,q) ->
             (FStar_Syntax_Unionfind.commit tx;
              FStar_Tactics_Result.Success ((FStar_Util.Inr a), q))
         | FStar_Tactics_Result.Failed (m,uu____768) ->
             (FStar_Syntax_Unionfind.rollback tx;
              FStar_Tactics_Result.Success ((FStar_Util.Inl m), ps)))
  
let trytac : 'a . 'a tac -> 'a FStar_Pervasives_Native.option tac =
  fun t  ->
    let uu____793 = trytac' t  in
    bind uu____793
      (fun r  ->
         match r with
         | FStar_Util.Inr v1 -> ret (FStar_Pervasives_Native.Some v1)
         | FStar_Util.Inl uu____820 -> ret FStar_Pervasives_Native.None)
  
let wrap_err : 'a . Prims.string -> 'a tac -> 'a tac =
  fun pref  ->
    fun t  ->
      mk_tac
        (fun ps  ->
           let uu____846 = run t ps  in
           match uu____846 with
           | FStar_Tactics_Result.Success (a,q) ->
               FStar_Tactics_Result.Success (a, q)
           | FStar_Tactics_Result.Failed (msg,q) ->
               FStar_Tactics_Result.Failed
                 ((Prims.strcat pref (Prims.strcat ": " msg)), q))
  
let (set : FStar_Tactics_Types.proofstate -> Prims.unit tac) =
  fun p  -> mk_tac (fun uu____863  -> FStar_Tactics_Result.Success ((), p)) 
let (do_unify :
  env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let debug_on uu____876 =
          let uu____877 =
            FStar_Options.set_options FStar_Options.Set
              "--debug_level Rel --debug_level RelCheck"
             in
          ()  in
        let debug_off uu____881 =
          let uu____882 = FStar_Options.set_options FStar_Options.Reset ""
             in
          ()  in
        (let uu____884 =
           FStar_TypeChecker_Env.debug env (FStar_Options.Other "1346")  in
         if uu____884
         then
           (debug_on ();
            (let uu____886 = FStar_Syntax_Print.term_to_string t1  in
             let uu____887 = FStar_Syntax_Print.term_to_string t2  in
             FStar_Util.print2 "%%%%%%%%do_unify %s =? %s\n" uu____886
               uu____887))
         else ());
        (try
           let res = FStar_TypeChecker_Rel.teq_nosmt env t1 t2  in
           debug_off (); res
         with | uu____899 -> (debug_off (); false))
  
let (trysolve :
  FStar_Tactics_Types.goal -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun goal  ->
    fun solution  ->
      do_unify goal.FStar_Tactics_Types.context solution
        goal.FStar_Tactics_Types.witness
  
let (dismiss : Prims.unit tac) =
  bind get
    (fun p  ->
       let uu____912 =
         let uu___62_913 = p  in
         let uu____914 = FStar_List.tl p.FStar_Tactics_Types.goals  in
         {
           FStar_Tactics_Types.main_context =
             (uu___62_913.FStar_Tactics_Types.main_context);
           FStar_Tactics_Types.main_goal =
             (uu___62_913.FStar_Tactics_Types.main_goal);
           FStar_Tactics_Types.all_implicits =
             (uu___62_913.FStar_Tactics_Types.all_implicits);
           FStar_Tactics_Types.goals = uu____914;
           FStar_Tactics_Types.smt_goals =
             (uu___62_913.FStar_Tactics_Types.smt_goals);
           FStar_Tactics_Types.depth =
             (uu___62_913.FStar_Tactics_Types.depth);
           FStar_Tactics_Types.__dump =
             (uu___62_913.FStar_Tactics_Types.__dump);
           FStar_Tactics_Types.psc = (uu___62_913.FStar_Tactics_Types.psc);
           FStar_Tactics_Types.entry_range =
             (uu___62_913.FStar_Tactics_Types.entry_range)
         }  in
       set uu____912)
  
let (solve :
  FStar_Tactics_Types.goal -> FStar_Syntax_Syntax.term -> Prims.unit tac) =
  fun goal  ->
    fun solution  ->
      let uu____927 = trysolve goal solution  in
      if uu____927
      then dismiss
      else
        (let uu____931 =
           let uu____932 = tts goal.FStar_Tactics_Types.context solution  in
           let uu____933 =
             tts goal.FStar_Tactics_Types.context
               goal.FStar_Tactics_Types.witness
              in
           let uu____934 =
             tts goal.FStar_Tactics_Types.context
               goal.FStar_Tactics_Types.goal_ty
              in
           FStar_Util.format3 "%s does not solve %s : %s" uu____932 uu____933
             uu____934
            in
         fail uu____931)
  
let (dismiss_all : Prims.unit tac) =
  bind get
    (fun p  ->
       set
         (let uu___63_941 = p  in
          {
            FStar_Tactics_Types.main_context =
              (uu___63_941.FStar_Tactics_Types.main_context);
            FStar_Tactics_Types.main_goal =
              (uu___63_941.FStar_Tactics_Types.main_goal);
            FStar_Tactics_Types.all_implicits =
              (uu___63_941.FStar_Tactics_Types.all_implicits);
            FStar_Tactics_Types.goals = [];
            FStar_Tactics_Types.smt_goals =
              (uu___63_941.FStar_Tactics_Types.smt_goals);
            FStar_Tactics_Types.depth =
              (uu___63_941.FStar_Tactics_Types.depth);
            FStar_Tactics_Types.__dump =
              (uu___63_941.FStar_Tactics_Types.__dump);
            FStar_Tactics_Types.psc = (uu___63_941.FStar_Tactics_Types.psc);
            FStar_Tactics_Types.entry_range =
              (uu___63_941.FStar_Tactics_Types.entry_range)
          }))
  
let (nwarn : Prims.int FStar_ST.ref) =
  FStar_Util.mk_ref (Prims.parse_int "0") 
let (check_valid_goal : FStar_Tactics_Types.goal -> Prims.unit) =
  fun g  ->
    let b = true  in
    let env = g.FStar_Tactics_Types.context  in
    let b1 =
      b && (FStar_TypeChecker_Env.closed env g.FStar_Tactics_Types.witness)
       in
    let b2 =
      b1 && (FStar_TypeChecker_Env.closed env g.FStar_Tactics_Types.goal_ty)
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
    if uu____1013
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
          (g.FStar_Tactics_Types.goal_ty).FStar_Syntax_Syntax.pos uu____1039);
       (let uu____1046 =
          let uu____1047 = FStar_ST.op_Bang nwarn  in
          uu____1047 + (Prims.parse_int "1")  in
        FStar_ST.op_Colon_Equals nwarn uu____1046))
    else ()
  
let (add_goals : FStar_Tactics_Types.goal Prims.list -> Prims.unit tac) =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___64_1104 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___64_1104.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___64_1104.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___64_1104.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (FStar_List.append gs p.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___64_1104.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___64_1104.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___64_1104.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___64_1104.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___64_1104.FStar_Tactics_Types.entry_range)
            }))
  
let (add_smt_goals : FStar_Tactics_Types.goal Prims.list -> Prims.unit tac) =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___65_1122 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___65_1122.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___65_1122.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___65_1122.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___65_1122.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (FStar_List.append gs p.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___65_1122.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___65_1122.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___65_1122.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___65_1122.FStar_Tactics_Types.entry_range)
            }))
  
let (push_goals : FStar_Tactics_Types.goal Prims.list -> Prims.unit tac) =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___66_1140 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___66_1140.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___66_1140.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___66_1140.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (FStar_List.append p.FStar_Tactics_Types.goals gs);
              FStar_Tactics_Types.smt_goals =
                (uu___66_1140.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___66_1140.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___66_1140.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___66_1140.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___66_1140.FStar_Tactics_Types.entry_range)
            }))
  
let (push_smt_goals : FStar_Tactics_Types.goal Prims.list -> Prims.unit tac)
  =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___67_1158 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___67_1158.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___67_1158.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___67_1158.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___67_1158.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (FStar_List.append p.FStar_Tactics_Types.smt_goals gs);
              FStar_Tactics_Types.depth =
                (uu___67_1158.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___67_1158.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___67_1158.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___67_1158.FStar_Tactics_Types.entry_range)
            }))
  
let (replace_cur : FStar_Tactics_Types.goal -> Prims.unit tac) =
  fun g  -> bind dismiss (fun uu____1167  -> add_goals [g]) 
let (add_implicits : implicits -> Prims.unit tac) =
  fun i  ->
    bind get
      (fun p  ->
         set
           (let uu___68_1179 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___68_1179.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___68_1179.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (FStar_List.append i p.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___68_1179.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___68_1179.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___68_1179.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___68_1179.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___68_1179.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___68_1179.FStar_Tactics_Types.entry_range)
            }))
  
let (new_uvar :
  Prims.string ->
    env -> FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.term tac)
  =
  fun reason  ->
    fun env  ->
      fun typ  ->
        let uu____1205 =
          FStar_TypeChecker_Util.new_implicit_var reason
            typ.FStar_Syntax_Syntax.pos env typ
           in
        match uu____1205 with
        | (u,uu____1221,g_u) ->
            let uu____1235 =
              add_implicits g_u.FStar_TypeChecker_Env.implicits  in
            bind uu____1235 (fun uu____1239  -> ret u)
  
let (is_true : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____1243 = FStar_Syntax_Util.un_squash t  in
    match uu____1243 with
    | FStar_Pervasives_Native.Some t' ->
        let uu____1253 =
          let uu____1254 = FStar_Syntax_Subst.compress t'  in
          uu____1254.FStar_Syntax_Syntax.n  in
        (match uu____1253 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.true_lid
         | uu____1258 -> false)
    | uu____1259 -> false
  
let (is_false : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____1267 = FStar_Syntax_Util.un_squash t  in
    match uu____1267 with
    | FStar_Pervasives_Native.Some t' ->
        let uu____1277 =
          let uu____1278 = FStar_Syntax_Subst.compress t'  in
          uu____1278.FStar_Syntax_Syntax.n  in
        (match uu____1277 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.false_lid
         | uu____1282 -> false)
    | uu____1283 -> false
  
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
            let uu____1323 = env.FStar_TypeChecker_Env.universe_of env phi
               in
            FStar_Syntax_Util.mk_squash uu____1323 phi  in
          let uu____1324 = new_uvar reason env typ  in
          bind uu____1324
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
             let uu____1380 =
               (ps.FStar_Tactics_Types.main_context).FStar_TypeChecker_Env.type_of
                 e t
                in
             ret uu____1380
           with | e1 -> fail "not typeable")
  
let (must_trivial : env -> FStar_TypeChecker_Env.guard_t -> Prims.unit tac) =
  fun e  ->
    fun g  ->
      try
        let uu____1428 =
          let uu____1429 =
            let uu____1430 = FStar_TypeChecker_Rel.discharge_guard_no_smt e g
               in
            FStar_All.pipe_left FStar_TypeChecker_Rel.is_trivial uu____1430
             in
          Prims.op_Negation uu____1429  in
        if uu____1428 then fail "got non-trivial guard" else ret ()
      with | uu____1439 -> fail "got non-trivial guard"
  
let (tc : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.typ tac) =
  fun t  ->
    let uu____1447 =
      bind cur_goal
        (fun goal  ->
           let uu____1453 = __tc goal.FStar_Tactics_Types.context t  in
           bind uu____1453
             (fun uu____1473  ->
                match uu____1473 with
                | (t1,typ,guard) ->
                    let uu____1485 =
                      must_trivial goal.FStar_Tactics_Types.context guard  in
                    bind uu____1485 (fun uu____1489  -> ret typ)))
       in
    FStar_All.pipe_left (wrap_err "tc") uu____1447
  
let (add_irrelevant_goal :
  Prims.string ->
    env ->
      FStar_Syntax_Syntax.typ -> FStar_Options.optionstate -> Prims.unit tac)
  =
  fun reason  ->
    fun env  ->
      fun phi  ->
        fun opts  ->
          let uu____1510 = mk_irrelevant_goal reason env phi opts  in
          bind uu____1510 (fun goal  -> add_goals [goal])
  
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
       let uu____1532 =
         istrivial goal.FStar_Tactics_Types.context
           goal.FStar_Tactics_Types.goal_ty
          in
       if uu____1532
       then solve goal FStar_Syntax_Util.exp_unit
       else
         (let uu____1536 =
            tts goal.FStar_Tactics_Types.context
              goal.FStar_Tactics_Types.goal_ty
             in
          fail1 "Not a trivial goal: %s" uu____1536))
  
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
          let uu____1553 =
            let uu____1554 = FStar_TypeChecker_Rel.simplify_guard e g  in
            uu____1554.FStar_TypeChecker_Env.guard_f  in
          match uu____1553 with
          | FStar_TypeChecker_Common.Trivial  -> ret ()
          | FStar_TypeChecker_Common.NonTrivial f ->
              let uu____1558 = istrivial e f  in
              if uu____1558
              then ret ()
              else
                (let uu____1562 = mk_irrelevant_goal reason e f opts  in
                 bind uu____1562
                   (fun goal  ->
                      let goal1 =
                        let uu___73_1569 = goal  in
                        {
                          FStar_Tactics_Types.context =
                            (uu___73_1569.FStar_Tactics_Types.context);
                          FStar_Tactics_Types.witness =
                            (uu___73_1569.FStar_Tactics_Types.witness);
                          FStar_Tactics_Types.goal_ty =
                            (uu___73_1569.FStar_Tactics_Types.goal_ty);
                          FStar_Tactics_Types.opts =
                            (uu___73_1569.FStar_Tactics_Types.opts);
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
          let uu____1590 =
            let uu____1591 = FStar_TypeChecker_Rel.simplify_guard e g  in
            uu____1591.FStar_TypeChecker_Env.guard_f  in
          match uu____1590 with
          | FStar_TypeChecker_Common.Trivial  ->
              ret FStar_Pervasives_Native.None
          | FStar_TypeChecker_Common.NonTrivial f ->
              let uu____1599 = istrivial e f  in
              if uu____1599
              then ret FStar_Pervasives_Native.None
              else
                (let uu____1607 = mk_irrelevant_goal reason e f opts  in
                 bind uu____1607
                   (fun goal  ->
                      ret
                        (FStar_Pervasives_Native.Some
                           (let uu___74_1617 = goal  in
                            {
                              FStar_Tactics_Types.context =
                                (uu___74_1617.FStar_Tactics_Types.context);
                              FStar_Tactics_Types.witness =
                                (uu___74_1617.FStar_Tactics_Types.witness);
                              FStar_Tactics_Types.goal_ty =
                                (uu___74_1617.FStar_Tactics_Types.goal_ty);
                              FStar_Tactics_Types.opts =
                                (uu___74_1617.FStar_Tactics_Types.opts);
                              FStar_Tactics_Types.is_guard = true
                            }))))
  
let (smt : Prims.unit tac) =
  bind cur_goal
    (fun g  ->
       let uu____1625 = is_irrelevant g  in
       if uu____1625
       then bind dismiss (fun uu____1629  -> add_smt_goals [g])
       else
         (let uu____1631 =
            tts g.FStar_Tactics_Types.context g.FStar_Tactics_Types.goal_ty
             in
          fail1 "goal is not irrelevant: cannot dispatch to smt (%s)"
            uu____1631))
  
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
             let uu____1672 =
               try
                 let uu____1706 =
                   let uu____1715 = FStar_BigInt.to_int_fs n1  in
                   FStar_List.splitAt uu____1715 p.FStar_Tactics_Types.goals
                    in
                 ret uu____1706
               with | uu____1737 -> fail "divide: not enough goals"  in
             bind uu____1672
               (fun uu____1764  ->
                  match uu____1764 with
                  | (lgs,rgs) ->
                      let lp =
                        let uu___75_1790 = p  in
                        {
                          FStar_Tactics_Types.main_context =
                            (uu___75_1790.FStar_Tactics_Types.main_context);
                          FStar_Tactics_Types.main_goal =
                            (uu___75_1790.FStar_Tactics_Types.main_goal);
                          FStar_Tactics_Types.all_implicits =
                            (uu___75_1790.FStar_Tactics_Types.all_implicits);
                          FStar_Tactics_Types.goals = lgs;
                          FStar_Tactics_Types.smt_goals = [];
                          FStar_Tactics_Types.depth =
                            (uu___75_1790.FStar_Tactics_Types.depth);
                          FStar_Tactics_Types.__dump =
                            (uu___75_1790.FStar_Tactics_Types.__dump);
                          FStar_Tactics_Types.psc =
                            (uu___75_1790.FStar_Tactics_Types.psc);
                          FStar_Tactics_Types.entry_range =
                            (uu___75_1790.FStar_Tactics_Types.entry_range)
                        }  in
                      let rp =
                        let uu___76_1792 = p  in
                        {
                          FStar_Tactics_Types.main_context =
                            (uu___76_1792.FStar_Tactics_Types.main_context);
                          FStar_Tactics_Types.main_goal =
                            (uu___76_1792.FStar_Tactics_Types.main_goal);
                          FStar_Tactics_Types.all_implicits =
                            (uu___76_1792.FStar_Tactics_Types.all_implicits);
                          FStar_Tactics_Types.goals = rgs;
                          FStar_Tactics_Types.smt_goals = [];
                          FStar_Tactics_Types.depth =
                            (uu___76_1792.FStar_Tactics_Types.depth);
                          FStar_Tactics_Types.__dump =
                            (uu___76_1792.FStar_Tactics_Types.__dump);
                          FStar_Tactics_Types.psc =
                            (uu___76_1792.FStar_Tactics_Types.psc);
                          FStar_Tactics_Types.entry_range =
                            (uu___76_1792.FStar_Tactics_Types.entry_range)
                        }  in
                      let uu____1793 = set lp  in
                      bind uu____1793
                        (fun uu____1801  ->
                           bind l
                             (fun a  ->
                                bind get
                                  (fun lp'  ->
                                     let uu____1815 = set rp  in
                                     bind uu____1815
                                       (fun uu____1823  ->
                                          bind r
                                            (fun b  ->
                                               bind get
                                                 (fun rp'  ->
                                                    let p' =
                                                      let uu___77_1839 = p
                                                         in
                                                      {
                                                        FStar_Tactics_Types.main_context
                                                          =
                                                          (uu___77_1839.FStar_Tactics_Types.main_context);
                                                        FStar_Tactics_Types.main_goal
                                                          =
                                                          (uu___77_1839.FStar_Tactics_Types.main_goal);
                                                        FStar_Tactics_Types.all_implicits
                                                          =
                                                          (uu___77_1839.FStar_Tactics_Types.all_implicits);
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
                                                          (uu___77_1839.FStar_Tactics_Types.depth);
                                                        FStar_Tactics_Types.__dump
                                                          =
                                                          (uu___77_1839.FStar_Tactics_Types.__dump);
                                                        FStar_Tactics_Types.psc
                                                          =
                                                          (uu___77_1839.FStar_Tactics_Types.psc);
                                                        FStar_Tactics_Types.entry_range
                                                          =
                                                          (uu___77_1839.FStar_Tactics_Types.entry_range)
                                                      }  in
                                                    let uu____1840 = set p'
                                                       in
                                                    bind uu____1840
                                                      (fun uu____1848  ->
                                                         ret (a, b))))))))))
  
let focus : 'a . 'a tac -> 'a tac =
  fun f  ->
    let uu____1866 = divide FStar_BigInt.one f idtac  in
    bind uu____1866
      (fun uu____1879  -> match uu____1879 with | (a,()) -> ret a)
  
let rec map : 'a . 'a tac -> 'a Prims.list tac =
  fun tau  ->
    bind get
      (fun p  ->
         match p.FStar_Tactics_Types.goals with
         | [] -> ret []
         | uu____1913::uu____1914 ->
             let uu____1917 =
               let uu____1926 = map tau  in
               divide FStar_BigInt.one tau uu____1926  in
             bind uu____1917
               (fun uu____1944  ->
                  match uu____1944 with | (h,t) -> ret (h :: t)))
  
let (seq : Prims.unit tac -> Prims.unit tac -> Prims.unit tac) =
  fun t1  ->
    fun t2  ->
      let uu____1981 =
        bind t1
          (fun uu____1986  ->
             let uu____1987 = map t2  in
             bind uu____1987 (fun uu____1995  -> ret ()))
         in
      focus uu____1981
  
let (intro : FStar_Syntax_Syntax.binder tac) =
  bind cur_goal
    (fun goal  ->
       let uu____2008 =
         FStar_Syntax_Util.arrow_one goal.FStar_Tactics_Types.goal_ty  in
       match uu____2008 with
       | FStar_Pervasives_Native.Some (b,c) ->
           let uu____2023 =
             let uu____2024 = FStar_Syntax_Util.is_total_comp c  in
             Prims.op_Negation uu____2024  in
           if uu____2023
           then fail "Codomain is effectful"
           else
             (let env' =
                FStar_TypeChecker_Env.push_binders
                  goal.FStar_Tactics_Types.context [b]
                 in
              let typ' = comp_to_typ c  in
              let uu____2030 = new_uvar "intro" env' typ'  in
              bind uu____2030
                (fun u  ->
                   let uu____2037 =
                     let uu____2038 =
                       FStar_Syntax_Util.abs [b] u
                         FStar_Pervasives_Native.None
                        in
                     trysolve goal uu____2038  in
                   if uu____2037
                   then
                     let uu____2041 =
                       let uu____2044 =
                         let uu___80_2045 = goal  in
                         let uu____2046 = bnorm env' u  in
                         let uu____2047 = bnorm env' typ'  in
                         {
                           FStar_Tactics_Types.context = env';
                           FStar_Tactics_Types.witness = uu____2046;
                           FStar_Tactics_Types.goal_ty = uu____2047;
                           FStar_Tactics_Types.opts =
                             (uu___80_2045.FStar_Tactics_Types.opts);
                           FStar_Tactics_Types.is_guard =
                             (uu___80_2045.FStar_Tactics_Types.is_guard)
                         }  in
                       replace_cur uu____2044  in
                     bind uu____2041 (fun uu____2049  -> ret b)
                   else fail "intro: unification failed"))
       | FStar_Pervasives_Native.None  ->
           let uu____2055 =
             tts goal.FStar_Tactics_Types.context
               goal.FStar_Tactics_Types.goal_ty
              in
           fail1 "intro: goal is not an arrow (%s)" uu____2055)
  
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
       (let uu____2082 =
          FStar_Syntax_Util.arrow_one goal.FStar_Tactics_Types.goal_ty  in
        match uu____2082 with
        | FStar_Pervasives_Native.Some (b,c) ->
            let uu____2101 =
              let uu____2102 = FStar_Syntax_Util.is_total_comp c  in
              Prims.op_Negation uu____2102  in
            if uu____2101
            then fail "Codomain is effectful"
            else
              (let bv =
                 FStar_Syntax_Syntax.gen_bv "__recf"
                   FStar_Pervasives_Native.None
                   goal.FStar_Tactics_Types.goal_ty
                  in
               let bs =
                 let uu____2118 = FStar_Syntax_Syntax.mk_binder bv  in
                 [uu____2118; b]  in
               let env' =
                 FStar_TypeChecker_Env.push_binders
                   goal.FStar_Tactics_Types.context bs
                  in
               let uu____2120 =
                 let uu____2123 = comp_to_typ c  in
                 new_uvar "intro_rec" env' uu____2123  in
               bind uu____2120
                 (fun u  ->
                    let lb =
                      let uu____2139 =
                        FStar_Syntax_Util.abs [b] u
                          FStar_Pervasives_Native.None
                         in
                      FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl bv) []
                        goal.FStar_Tactics_Types.goal_ty
                        FStar_Parser_Const.effect_Tot_lid uu____2139
                       in
                    let body = FStar_Syntax_Syntax.bv_to_name bv  in
                    let uu____2143 =
                      FStar_Syntax_Subst.close_let_rec [lb] body  in
                    match uu____2143 with
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
                          let uu____2180 =
                            let uu____2183 =
                              let uu___81_2184 = goal  in
                              let uu____2185 = bnorm env' u  in
                              let uu____2186 =
                                let uu____2187 = comp_to_typ c  in
                                bnorm env' uu____2187  in
                              {
                                FStar_Tactics_Types.context = env';
                                FStar_Tactics_Types.witness = uu____2185;
                                FStar_Tactics_Types.goal_ty = uu____2186;
                                FStar_Tactics_Types.opts =
                                  (uu___81_2184.FStar_Tactics_Types.opts);
                                FStar_Tactics_Types.is_guard =
                                  (uu___81_2184.FStar_Tactics_Types.is_guard)
                              }  in
                            replace_cur uu____2183  in
                          bind uu____2180
                            (fun uu____2194  ->
                               let uu____2195 =
                                 let uu____2200 =
                                   FStar_Syntax_Syntax.mk_binder bv  in
                                 (uu____2200, b)  in
                               ret uu____2195)
                        else fail "intro_rec: unification failed"))
        | FStar_Pervasives_Native.None  ->
            let uu____2214 =
              tts goal.FStar_Tactics_Types.context
                goal.FStar_Tactics_Types.goal_ty
               in
            fail1 "intro_rec: goal is not an arrow (%s)" uu____2214))
  
let (norm : FStar_Syntax_Embeddings.norm_step Prims.list -> Prims.unit tac) =
  fun s  ->
    bind cur_goal
      (fun goal  ->
         mlog
           (fun uu____2234  ->
              let uu____2235 =
                FStar_Syntax_Print.term_to_string
                  goal.FStar_Tactics_Types.witness
                 in
              FStar_Util.print1 "norm: witness = %s\n" uu____2235)
           (fun uu____2240  ->
              let steps =
                let uu____2244 = FStar_TypeChecker_Normalize.tr_norm_steps s
                   in
                FStar_List.append
                  [FStar_TypeChecker_Normalize.Reify;
                  FStar_TypeChecker_Normalize.UnfoldTac] uu____2244
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
                (let uu___82_2251 = goal  in
                 {
                   FStar_Tactics_Types.context =
                     (uu___82_2251.FStar_Tactics_Types.context);
                   FStar_Tactics_Types.witness = w;
                   FStar_Tactics_Types.goal_ty = t;
                   FStar_Tactics_Types.opts =
                     (uu___82_2251.FStar_Tactics_Types.opts);
                   FStar_Tactics_Types.is_guard =
                     (uu___82_2251.FStar_Tactics_Types.is_guard)
                 })))
  
let (norm_term_env :
  env ->
    FStar_Syntax_Embeddings.norm_step Prims.list ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac)
  =
  fun e  ->
    fun s  ->
      fun t  ->
        let uu____2269 =
          mlog
            (fun uu____2274  ->
               let uu____2275 = FStar_Syntax_Print.term_to_string t  in
               FStar_Util.print1 "norm_term: tm = %s\n" uu____2275)
            (fun uu____2277  ->
               bind get
                 (fun ps  ->
                    let uu____2281 = __tc e t  in
                    bind uu____2281
                      (fun uu____2303  ->
                         match uu____2303 with
                         | (t1,uu____2313,guard) ->
                             (FStar_TypeChecker_Rel.force_trivial_guard e
                                guard;
                              (let steps =
                                 let uu____2319 =
                                   FStar_TypeChecker_Normalize.tr_norm_steps
                                     s
                                    in
                                 FStar_List.append
                                   [FStar_TypeChecker_Normalize.Reify;
                                   FStar_TypeChecker_Normalize.UnfoldTac]
                                   uu____2319
                                  in
                               let t2 =
                                 normalize steps
                                   ps.FStar_Tactics_Types.main_context t1
                                  in
                               ret t2)))))
           in
        FStar_All.pipe_left (wrap_err "norm_term") uu____2269
  
let (refine_intro : Prims.unit tac) =
  let uu____2331 =
    bind cur_goal
      (fun g  ->
         let uu____2338 =
           FStar_TypeChecker_Rel.base_and_refinement
             g.FStar_Tactics_Types.context g.FStar_Tactics_Types.goal_ty
            in
         match uu____2338 with
         | (uu____2351,FStar_Pervasives_Native.None ) ->
             fail "not a refinement"
         | (t,FStar_Pervasives_Native.Some (bv,phi)) ->
             let g1 =
               let uu___83_2376 = g  in
               {
                 FStar_Tactics_Types.context =
                   (uu___83_2376.FStar_Tactics_Types.context);
                 FStar_Tactics_Types.witness =
                   (uu___83_2376.FStar_Tactics_Types.witness);
                 FStar_Tactics_Types.goal_ty = t;
                 FStar_Tactics_Types.opts =
                   (uu___83_2376.FStar_Tactics_Types.opts);
                 FStar_Tactics_Types.is_guard =
                   (uu___83_2376.FStar_Tactics_Types.is_guard)
               }  in
             let uu____2377 =
               let uu____2382 =
                 let uu____2387 =
                   let uu____2388 = FStar_Syntax_Syntax.mk_binder bv  in
                   [uu____2388]  in
                 FStar_Syntax_Subst.open_term uu____2387 phi  in
               match uu____2382 with
               | (bvs,phi1) ->
                   let uu____2395 =
                     let uu____2396 = FStar_List.hd bvs  in
                     FStar_Pervasives_Native.fst uu____2396  in
                   (uu____2395, phi1)
                in
             (match uu____2377 with
              | (bv1,phi1) ->
                  let uu____2409 =
                    let uu____2412 =
                      FStar_Syntax_Subst.subst
                        [FStar_Syntax_Syntax.NT
                           (bv1, (g.FStar_Tactics_Types.witness))] phi1
                       in
                    mk_irrelevant_goal "refine_intro refinement"
                      g.FStar_Tactics_Types.context uu____2412
                      g.FStar_Tactics_Types.opts
                     in
                  bind uu____2409
                    (fun g2  ->
                       bind dismiss (fun uu____2416  -> add_goals [g1; g2]))))
     in
  FStar_All.pipe_left (wrap_err "refine_intro") uu____2331 
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
             let uu____2440 = __tc env t  in
             bind uu____2440
               (fun uu____2460  ->
                  match uu____2460 with
                  | (t1,typ,guard) ->
                      let uu____2472 =
                        if force_guard
                        then
                          must_trivial goal.FStar_Tactics_Types.context guard
                        else
                          add_goal_from_guard "__exact typing"
                            goal.FStar_Tactics_Types.context guard
                            goal.FStar_Tactics_Types.opts
                         in
                      bind uu____2472
                        (fun uu____2479  ->
                           mlog
                             (fun uu____2483  ->
                                let uu____2484 =
                                  tts goal.FStar_Tactics_Types.context typ
                                   in
                                let uu____2485 =
                                  tts goal.FStar_Tactics_Types.context
                                    goal.FStar_Tactics_Types.goal_ty
                                   in
                                FStar_Util.print2
                                  "exact: unifying %s and %s\n" uu____2484
                                  uu____2485)
                             (fun uu____2488  ->
                                let uu____2489 =
                                  do_unify goal.FStar_Tactics_Types.context
                                    typ goal.FStar_Tactics_Types.goal_ty
                                   in
                                if uu____2489
                                then solve goal t1
                                else
                                  (let uu____2493 =
                                     tts goal.FStar_Tactics_Types.context t1
                                      in
                                   let uu____2494 =
                                     tts goal.FStar_Tactics_Types.context typ
                                      in
                                   let uu____2495 =
                                     tts goal.FStar_Tactics_Types.context
                                       goal.FStar_Tactics_Types.goal_ty
                                      in
                                   fail3
                                     "%s : %s does not exactly solve the goal %s"
                                     uu____2493 uu____2494 uu____2495)))))
  
let (t_exact :
  Prims.bool -> Prims.bool -> FStar_Syntax_Syntax.term -> Prims.unit tac) =
  fun set_expected_typ1  ->
    fun force_guard  ->
      fun tm  ->
        let uu____2509 =
          mlog
            (fun uu____2514  ->
               let uu____2515 = FStar_Syntax_Print.term_to_string tm  in
               FStar_Util.print1 "t_exact: tm = %s\n" uu____2515)
            (fun uu____2518  ->
               let uu____2519 =
                 let uu____2526 =
                   __exact_now set_expected_typ1 force_guard tm  in
                 trytac' uu____2526  in
               bind uu____2519
                 (fun uu___57_2535  ->
                    match uu___57_2535 with
                    | FStar_Util.Inr r -> ret ()
                    | FStar_Util.Inl e ->
                        let uu____2544 =
                          let uu____2551 =
                            let uu____2554 =
                              norm [FStar_Syntax_Embeddings.Delta]  in
                            bind uu____2554
                              (fun uu____2558  ->
                                 bind refine_intro
                                   (fun uu____2560  ->
                                      __exact_now set_expected_typ1
                                        force_guard tm))
                             in
                          trytac' uu____2551  in
                        bind uu____2544
                          (fun uu___56_2567  ->
                             match uu___56_2567 with
                             | FStar_Util.Inr r -> ret ()
                             | FStar_Util.Inl uu____2575 -> fail e)))
           in
        FStar_All.pipe_left (wrap_err "exact") uu____2509
  
let (uvar_free_in_goal :
  FStar_Syntax_Syntax.uvar -> FStar_Tactics_Types.goal -> Prims.bool) =
  fun u  ->
    fun g  ->
      if g.FStar_Tactics_Types.is_guard
      then false
      else
        (let free_uvars =
           let uu____2590 =
             let uu____2597 =
               FStar_Syntax_Free.uvars g.FStar_Tactics_Types.goal_ty  in
             FStar_Util.set_elements uu____2597  in
           FStar_List.map FStar_Pervasives_Native.fst uu____2590  in
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
          let uu____2657 = f x  in
          bind uu____2657
            (fun y  ->
               let uu____2665 = mapM f xs  in
               bind uu____2665 (fun ys  -> ret (y :: ys)))
  
exception NoUnif 
let (uu___is_NoUnif : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with | NoUnif  -> true | uu____2683 -> false
  
let rec (__apply :
  Prims.bool ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.typ -> Prims.unit tac)
  =
  fun uopt  ->
    fun tm  ->
      fun typ  ->
        bind cur_goal
          (fun goal  ->
             let uu____2700 =
               let uu____2705 = t_exact false true tm  in trytac uu____2705
                in
             bind uu____2700
               (fun uu___58_2712  ->
                  match uu___58_2712 with
                  | FStar_Pervasives_Native.Some r -> ret ()
                  | FStar_Pervasives_Native.None  ->
                      let uu____2718 = FStar_Syntax_Util.arrow_one typ  in
                      (match uu____2718 with
                       | FStar_Pervasives_Native.None  ->
                           FStar_Exn.raise NoUnif
                       | FStar_Pervasives_Native.Some ((bv,aq),c) ->
                           mlog
                             (fun uu____2750  ->
                                let uu____2751 =
                                  FStar_Syntax_Print.binder_to_string
                                    (bv, aq)
                                   in
                                FStar_Util.print1
                                  "__apply: pushing binder %s\n" uu____2751)
                             (fun uu____2754  ->
                                let uu____2755 =
                                  let uu____2756 =
                                    FStar_Syntax_Util.is_total_comp c  in
                                  Prims.op_Negation uu____2756  in
                                if uu____2755
                                then fail "apply: not total codomain"
                                else
                                  (let uu____2760 =
                                     new_uvar "apply"
                                       goal.FStar_Tactics_Types.context
                                       bv.FStar_Syntax_Syntax.sort
                                      in
                                   bind uu____2760
                                     (fun u  ->
                                        let tm' =
                                          FStar_Syntax_Syntax.mk_Tm_app tm
                                            [(u, aq)]
                                            FStar_Pervasives_Native.None
                                            (goal.FStar_Tactics_Types.context).FStar_TypeChecker_Env.range
                                           in
                                        let typ' =
                                          let uu____2780 = comp_to_typ c  in
                                          FStar_All.pipe_left
                                            (FStar_Syntax_Subst.subst
                                               [FStar_Syntax_Syntax.NT
                                                  (bv, u)]) uu____2780
                                           in
                                        let uu____2781 =
                                          __apply uopt tm' typ'  in
                                        bind uu____2781
                                          (fun uu____2789  ->
                                             let u1 =
                                               bnorm
                                                 goal.FStar_Tactics_Types.context
                                                 u
                                                in
                                             let uu____2791 =
                                               let uu____2792 =
                                                 let uu____2795 =
                                                   let uu____2796 =
                                                     FStar_Syntax_Util.head_and_args
                                                       u1
                                                      in
                                                   FStar_Pervasives_Native.fst
                                                     uu____2796
                                                    in
                                                 FStar_Syntax_Subst.compress
                                                   uu____2795
                                                  in
                                               uu____2792.FStar_Syntax_Syntax.n
                                                in
                                             match uu____2791 with
                                             | FStar_Syntax_Syntax.Tm_uvar
                                                 (uvar,uu____2824) ->
                                                 bind get
                                                   (fun ps  ->
                                                      let uu____2852 =
                                                        uopt &&
                                                          (uvar_free uvar ps)
                                                         in
                                                      if uu____2852
                                                      then ret ()
                                                      else
                                                        (let uu____2856 =
                                                           let uu____2859 =
                                                             let uu___84_2860
                                                               = goal  in
                                                             let uu____2861 =
                                                               bnorm
                                                                 goal.FStar_Tactics_Types.context
                                                                 u1
                                                                in
                                                             let uu____2862 =
                                                               bnorm
                                                                 goal.FStar_Tactics_Types.context
                                                                 bv.FStar_Syntax_Syntax.sort
                                                                in
                                                             {
                                                               FStar_Tactics_Types.context
                                                                 =
                                                                 (uu___84_2860.FStar_Tactics_Types.context);
                                                               FStar_Tactics_Types.witness
                                                                 = uu____2861;
                                                               FStar_Tactics_Types.goal_ty
                                                                 = uu____2862;
                                                               FStar_Tactics_Types.opts
                                                                 =
                                                                 (uu___84_2860.FStar_Tactics_Types.opts);
                                                               FStar_Tactics_Types.is_guard
                                                                 = false
                                                             }  in
                                                           [uu____2859]  in
                                                         add_goals uu____2856))
                                             | t -> ret ())))))))
  
let try_unif : 'a . 'a tac -> 'a tac -> 'a tac =
  fun t  ->
    fun t'  -> mk_tac (fun ps  -> try run t ps with | NoUnif  -> run t' ps)
  
let (apply : Prims.bool -> FStar_Syntax_Syntax.term -> Prims.unit tac) =
  fun uopt  ->
    fun tm  ->
      let uu____2908 =
        mlog
          (fun uu____2913  ->
             let uu____2914 = FStar_Syntax_Print.term_to_string tm  in
             FStar_Util.print1 "apply: tm = %s\n" uu____2914)
          (fun uu____2916  ->
             bind cur_goal
               (fun goal  ->
                  let uu____2920 = __tc goal.FStar_Tactics_Types.context tm
                     in
                  bind uu____2920
                    (fun uu____2941  ->
                       match uu____2941 with
                       | (tm1,typ,guard) ->
                           let uu____2953 =
                             let uu____2956 =
                               let uu____2959 = __apply uopt tm1 typ  in
                               bind uu____2959
                                 (fun uu____2963  ->
                                    add_goal_from_guard "apply guard"
                                      goal.FStar_Tactics_Types.context guard
                                      goal.FStar_Tactics_Types.opts)
                                in
                             focus uu____2956  in
                           let uu____2964 =
                             let uu____2967 =
                               tts goal.FStar_Tactics_Types.context tm1  in
                             let uu____2968 =
                               tts goal.FStar_Tactics_Types.context typ  in
                             let uu____2969 =
                               tts goal.FStar_Tactics_Types.context
                                 goal.FStar_Tactics_Types.goal_ty
                                in
                             fail3
                               "Cannot instantiate %s (of type %s) to match goal (%s)"
                               uu____2967 uu____2968 uu____2969
                              in
                           try_unif uu____2953 uu____2964)))
         in
      FStar_All.pipe_left (wrap_err "apply") uu____2908
  
let (apply_lemma : FStar_Syntax_Syntax.term -> Prims.unit tac) =
  fun tm  ->
    let uu____2981 =
      let uu____2984 =
        mlog
          (fun uu____2989  ->
             let uu____2990 = FStar_Syntax_Print.term_to_string tm  in
             FStar_Util.print1 "apply_lemma: tm = %s\n" uu____2990)
          (fun uu____2993  ->
             let is_unit_t t =
               let uu____2998 =
                 let uu____2999 = FStar_Syntax_Subst.compress t  in
                 uu____2999.FStar_Syntax_Syntax.n  in
               match uu____2998 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.unit_lid
                   -> true
               | uu____3003 -> false  in
             bind cur_goal
               (fun goal  ->
                  let uu____3007 = __tc goal.FStar_Tactics_Types.context tm
                     in
                  bind uu____3007
                    (fun uu____3029  ->
                       match uu____3029 with
                       | (tm1,t,guard) ->
                           let uu____3041 =
                             FStar_Syntax_Util.arrow_formals_comp t  in
                           (match uu____3041 with
                            | (bs,comp) ->
                                if
                                  Prims.op_Negation
                                    (FStar_Syntax_Util.is_lemma_comp comp)
                                then fail "not a lemma"
                                else
                                  (let uu____3071 =
                                     FStar_List.fold_left
                                       (fun uu____3117  ->
                                          fun uu____3118  ->
                                            match (uu____3117, uu____3118)
                                            with
                                            | ((uvs,guard1,subst1),(b,aq)) ->
                                                let b_t =
                                                  FStar_Syntax_Subst.subst
                                                    subst1
                                                    b.FStar_Syntax_Syntax.sort
                                                   in
                                                let uu____3221 =
                                                  is_unit_t b_t  in
                                                if uu____3221
                                                then
                                                  (((FStar_Syntax_Util.exp_unit,
                                                      aq) :: uvs), guard1,
                                                    ((FStar_Syntax_Syntax.NT
                                                        (b,
                                                          FStar_Syntax_Util.exp_unit))
                                                    :: subst1))
                                                else
                                                  (let uu____3259 =
                                                     FStar_TypeChecker_Util.new_implicit_var
                                                       "apply_lemma"
                                                       (goal.FStar_Tactics_Types.goal_ty).FStar_Syntax_Syntax.pos
                                                       goal.FStar_Tactics_Types.context
                                                       b_t
                                                      in
                                                   match uu____3259 with
                                                   | (u,uu____3289,g_u) ->
                                                       let uu____3303 =
                                                         FStar_TypeChecker_Rel.conj_guard
                                                           guard1 g_u
                                                          in
                                                       (((u, aq) :: uvs),
                                                         uu____3303,
                                                         ((FStar_Syntax_Syntax.NT
                                                             (b, u)) ::
                                                         subst1))))
                                       ([], guard, []) bs
                                      in
                                   match uu____3071 with
                                   | (uvs,implicits,subst1) ->
                                       let uvs1 = FStar_List.rev uvs  in
                                       let comp1 =
                                         FStar_Syntax_Subst.subst_comp subst1
                                           comp
                                          in
                                       let uu____3373 =
                                         let uu____3382 =
                                           let uu____3391 =
                                             FStar_Syntax_Util.comp_to_comp_typ
                                               comp1
                                              in
                                           uu____3391.FStar_Syntax_Syntax.effect_args
                                            in
                                         match uu____3382 with
                                         | pre::post::uu____3402 ->
                                             ((FStar_Pervasives_Native.fst
                                                 pre),
                                               (FStar_Pervasives_Native.fst
                                                  post))
                                         | uu____3443 ->
                                             failwith
                                               "apply_lemma: impossible: not a lemma"
                                          in
                                       (match uu____3373 with
                                        | (pre,post) ->
                                            let post1 =
                                              let uu____3475 =
                                                let uu____3484 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    FStar_Syntax_Util.exp_unit
                                                   in
                                                [uu____3484]  in
                                              FStar_Syntax_Util.mk_app post
                                                uu____3475
                                               in
                                            let uu____3485 =
                                              let uu____3486 =
                                                let uu____3487 =
                                                  FStar_Syntax_Util.mk_squash
                                                    FStar_Syntax_Syntax.U_zero
                                                    post1
                                                   in
                                                do_unify
                                                  goal.FStar_Tactics_Types.context
                                                  uu____3487
                                                  goal.FStar_Tactics_Types.goal_ty
                                                 in
                                              Prims.op_Negation uu____3486
                                               in
                                            if uu____3485
                                            then
                                              let uu____3490 =
                                                tts
                                                  goal.FStar_Tactics_Types.context
                                                  tm1
                                                 in
                                              let uu____3491 =
                                                let uu____3492 =
                                                  FStar_Syntax_Util.mk_squash
                                                    FStar_Syntax_Syntax.U_zero
                                                    post1
                                                   in
                                                tts
                                                  goal.FStar_Tactics_Types.context
                                                  uu____3492
                                                 in
                                              let uu____3493 =
                                                tts
                                                  goal.FStar_Tactics_Types.context
                                                  goal.FStar_Tactics_Types.goal_ty
                                                 in
                                              fail3
                                                "Cannot instantiate lemma %s (with postcondition: %s) to match goal (%s)"
                                                uu____3490 uu____3491
                                                uu____3493
                                            else
                                              (let uu____3495 =
                                                 add_implicits
                                                   implicits.FStar_TypeChecker_Env.implicits
                                                  in
                                               bind uu____3495
                                                 (fun uu____3500  ->
                                                    let uu____3501 =
                                                      solve goal
                                                        FStar_Syntax_Util.exp_unit
                                                       in
                                                    bind uu____3501
                                                      (fun uu____3509  ->
                                                         let is_free_uvar uv
                                                           t1 =
                                                           let free_uvars =
                                                             let uu____3520 =
                                                               let uu____3527
                                                                 =
                                                                 FStar_Syntax_Free.uvars
                                                                   t1
                                                                  in
                                                               FStar_Util.set_elements
                                                                 uu____3527
                                                                in
                                                             FStar_List.map
                                                               FStar_Pervasives_Native.fst
                                                               uu____3520
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
                                                           let uu____3568 =
                                                             FStar_Syntax_Util.head_and_args
                                                               t1
                                                              in
                                                           match uu____3568
                                                           with
                                                           | (hd1,uu____3584)
                                                               ->
                                                               (match 
                                                                  hd1.FStar_Syntax_Syntax.n
                                                                with
                                                                | FStar_Syntax_Syntax.Tm_uvar
                                                                    (uv,uu____3606)
                                                                    ->
                                                                    appears
                                                                    uv goals
                                                                | uu____3631
                                                                    -> false)
                                                            in
                                                         let uu____3632 =
                                                           FStar_All.pipe_right
                                                             implicits.FStar_TypeChecker_Env.implicits
                                                             (mapM
                                                                (fun
                                                                   uu____3704
                                                                    ->
                                                                   match uu____3704
                                                                   with
                                                                   | 
                                                                   (_msg,env,_uvar,term,typ,uu____3732)
                                                                    ->
                                                                    let uu____3733
                                                                    =
                                                                    FStar_Syntax_Util.head_and_args
                                                                    term  in
                                                                    (match uu____3733
                                                                    with
                                                                    | 
                                                                    (hd1,uu____3759)
                                                                    ->
                                                                    let uu____3780
                                                                    =
                                                                    let uu____3781
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    hd1  in
                                                                    uu____3781.FStar_Syntax_Syntax.n
                                                                     in
                                                                    (match uu____3780
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Tm_uvar
                                                                    uu____3794
                                                                    ->
                                                                    let uu____3811
                                                                    =
                                                                    let uu____3820
                                                                    =
                                                                    let uu____3823
                                                                    =
                                                                    let uu___87_3824
                                                                    = goal
                                                                     in
                                                                    let uu____3825
                                                                    =
                                                                    bnorm
                                                                    goal.FStar_Tactics_Types.context
                                                                    term  in
                                                                    let uu____3826
                                                                    =
                                                                    bnorm
                                                                    goal.FStar_Tactics_Types.context
                                                                    typ  in
                                                                    {
                                                                    FStar_Tactics_Types.context
                                                                    =
                                                                    (uu___87_3824.FStar_Tactics_Types.context);
                                                                    FStar_Tactics_Types.witness
                                                                    =
                                                                    uu____3825;
                                                                    FStar_Tactics_Types.goal_ty
                                                                    =
                                                                    uu____3826;
                                                                    FStar_Tactics_Types.opts
                                                                    =
                                                                    (uu___87_3824.FStar_Tactics_Types.opts);
                                                                    FStar_Tactics_Types.is_guard
                                                                    =
                                                                    (uu___87_3824.FStar_Tactics_Types.is_guard)
                                                                    }  in
                                                                    [uu____3823]
                                                                     in
                                                                    (uu____3820,
                                                                    [])  in
                                                                    ret
                                                                    uu____3811
                                                                    | 
                                                                    uu____3839
                                                                    ->
                                                                    let g_typ
                                                                    =
                                                                    let uu____3841
                                                                    =
                                                                    FStar_Options.__temp_fast_implicits
                                                                    ()  in
                                                                    if
                                                                    uu____3841
                                                                    then
                                                                    FStar_TypeChecker_TcTerm.check_type_of_well_typed_term
                                                                    false env
                                                                    term typ
                                                                    else
                                                                    (let term1
                                                                    =
                                                                    bnorm env
                                                                    term  in
                                                                    let uu____3844
                                                                    =
                                                                    let uu____3851
                                                                    =
                                                                    FStar_TypeChecker_Env.set_expected_typ
                                                                    env typ
                                                                     in
                                                                    env.FStar_TypeChecker_Env.type_of
                                                                    uu____3851
                                                                    term1  in
                                                                    match uu____3844
                                                                    with
                                                                    | 
                                                                    (uu____3852,uu____3853,g_typ)
                                                                    -> g_typ)
                                                                     in
                                                                    let uu____3855
                                                                    =
                                                                    goal_from_guard
                                                                    "apply_lemma solved arg"
                                                                    goal.FStar_Tactics_Types.context
                                                                    g_typ
                                                                    goal.FStar_Tactics_Types.opts
                                                                     in
                                                                    bind
                                                                    uu____3855
                                                                    (fun
                                                                    uu___59_3871
                                                                     ->
                                                                    match uu___59_3871
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
                                                         bind uu____3632
                                                           (fun goals_  ->
                                                              let sub_goals =
                                                                let uu____3939
                                                                  =
                                                                  FStar_List.map
                                                                    FStar_Pervasives_Native.fst
                                                                    goals_
                                                                   in
                                                                FStar_List.flatten
                                                                  uu____3939
                                                                 in
                                                              let smt_goals =
                                                                let uu____3961
                                                                  =
                                                                  FStar_List.map
                                                                    FStar_Pervasives_Native.snd
                                                                    goals_
                                                                   in
                                                                FStar_List.flatten
                                                                  uu____3961
                                                                 in
                                                              let rec filter'
                                                                a f xs =
                                                                match xs with
                                                                | [] -> []
                                                                | x::xs1 ->
                                                                    let uu____4016
                                                                    = f x xs1
                                                                     in
                                                                    if
                                                                    uu____4016
                                                                    then
                                                                    let uu____4019
                                                                    =
                                                                    filter'
                                                                    () f xs1
                                                                     in x ::
                                                                    uu____4019
                                                                    else
                                                                    filter'
                                                                    () f xs1
                                                                 in
                                                              let sub_goals1
                                                                =
                                                                Obj.magic
                                                                  (filter' ()
                                                                    (fun a434
                                                                     ->
                                                                    fun a435 
                                                                    ->
                                                                    (Obj.magic
                                                                    (fun g 
                                                                    ->
                                                                    fun goals
                                                                     ->
                                                                    let uu____4033
                                                                    =
                                                                    checkone
                                                                    g.FStar_Tactics_Types.witness
                                                                    goals  in
                                                                    Prims.op_Negation
                                                                    uu____4033))
                                                                    a434 a435)
                                                                    (Obj.magic
                                                                    sub_goals))
                                                                 in
                                                              let uu____4034
                                                                =
                                                                add_goal_from_guard
                                                                  "apply_lemma guard"
                                                                  goal.FStar_Tactics_Types.context
                                                                  guard
                                                                  goal.FStar_Tactics_Types.opts
                                                                 in
                                                              bind uu____4034
                                                                (fun
                                                                   uu____4039
                                                                    ->
                                                                   let uu____4040
                                                                    =
                                                                    let uu____4043
                                                                    =
                                                                    let uu____4044
                                                                    =
                                                                    let uu____4045
                                                                    =
                                                                    FStar_Syntax_Util.mk_squash
                                                                    FStar_Syntax_Syntax.U_zero
                                                                    pre  in
                                                                    istrivial
                                                                    goal.FStar_Tactics_Types.context
                                                                    uu____4045
                                                                     in
                                                                    Prims.op_Negation
                                                                    uu____4044
                                                                     in
                                                                    if
                                                                    uu____4043
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
                                                                    uu____4040
                                                                    (fun
                                                                    uu____4051
                                                                     ->
                                                                    let uu____4052
                                                                    =
                                                                    add_smt_goals
                                                                    smt_goals
                                                                     in
                                                                    bind
                                                                    uu____4052
                                                                    (fun
                                                                    uu____4056
                                                                     ->
                                                                    add_goals
                                                                    sub_goals1)))))))))))))
         in
      focus uu____2984  in
    FStar_All.pipe_left (wrap_err "apply_lemma") uu____2981
  
let (destruct_eq' :
  FStar_Syntax_Syntax.typ ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun typ  ->
    let uu____4076 = FStar_Syntax_Util.destruct_typ_as_formula typ  in
    match uu____4076 with
    | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn
        (l,uu____4086::(e1,uu____4088)::(e2,uu____4090)::[])) when
        FStar_Ident.lid_equals l FStar_Parser_Const.eq2_lid ->
        FStar_Pervasives_Native.Some (e1, e2)
    | uu____4149 -> FStar_Pervasives_Native.None
  
let (destruct_eq :
  FStar_Syntax_Syntax.typ ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun typ  ->
    let uu____4171 = destruct_eq' typ  in
    match uu____4171 with
    | FStar_Pervasives_Native.Some t -> FStar_Pervasives_Native.Some t
    | FStar_Pervasives_Native.None  ->
        let uu____4201 = FStar_Syntax_Util.un_squash typ  in
        (match uu____4201 with
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
        let uu____4257 = FStar_TypeChecker_Env.pop_bv e1  in
        match uu____4257 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (bv',e') ->
            if FStar_Syntax_Syntax.bv_eq bvar bv'
            then FStar_Pervasives_Native.Some (e', [])
            else
              (let uu____4305 = aux e'  in
               FStar_Util.map_opt uu____4305
                 (fun uu____4329  ->
                    match uu____4329 with | (e'',bvs) -> (e'', (bv' :: bvs))))
         in
      let uu____4350 = aux e  in
      FStar_Util.map_opt uu____4350
        (fun uu____4374  ->
           match uu____4374 with | (e',bvs) -> (e', (FStar_List.rev bvs)))
  
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
          let uu____4429 = split_env b1 g.FStar_Tactics_Types.context  in
          FStar_Util.map_opt uu____4429
            (fun uu____4453  ->
               match uu____4453 with
               | (e0,bvs) ->
                   let s1 bv =
                     let uu___88_4470 = bv  in
                     let uu____4471 =
                       FStar_Syntax_Subst.subst s bv.FStar_Syntax_Syntax.sort
                        in
                     {
                       FStar_Syntax_Syntax.ppname =
                         (uu___88_4470.FStar_Syntax_Syntax.ppname);
                       FStar_Syntax_Syntax.index =
                         (uu___88_4470.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort = uu____4471
                     }  in
                   let bvs1 = FStar_List.map s1 bvs  in
                   let c = push_bvs e0 (b2 :: bvs1)  in
                   let w =
                     FStar_Syntax_Subst.subst s g.FStar_Tactics_Types.witness
                      in
                   let t =
                     FStar_Syntax_Subst.subst s g.FStar_Tactics_Types.goal_ty
                      in
                   let uu___89_4480 = g  in
                   {
                     FStar_Tactics_Types.context = c;
                     FStar_Tactics_Types.witness = w;
                     FStar_Tactics_Types.goal_ty = t;
                     FStar_Tactics_Types.opts =
                       (uu___89_4480.FStar_Tactics_Types.opts);
                     FStar_Tactics_Types.is_guard =
                       (uu___89_4480.FStar_Tactics_Types.is_guard)
                   })
  
let (rewrite : FStar_Syntax_Syntax.binder -> Prims.unit tac) =
  fun h  ->
    bind cur_goal
      (fun goal  ->
         let uu____4493 = h  in
         match uu____4493 with
         | (bv,uu____4497) ->
             mlog
               (fun uu____4501  ->
                  let uu____4502 = FStar_Syntax_Print.bv_to_string bv  in
                  let uu____4503 =
                    tts goal.FStar_Tactics_Types.context
                      bv.FStar_Syntax_Syntax.sort
                     in
                  FStar_Util.print2 "+++Rewrite %s : %s\n" uu____4502
                    uu____4503)
               (fun uu____4506  ->
                  let uu____4507 =
                    split_env bv goal.FStar_Tactics_Types.context  in
                  match uu____4507 with
                  | FStar_Pervasives_Native.None  ->
                      fail "rewrite: binder not found in environment"
                  | FStar_Pervasives_Native.Some (e0,bvs) ->
                      let uu____4536 =
                        destruct_eq bv.FStar_Syntax_Syntax.sort  in
                      (match uu____4536 with
                       | FStar_Pervasives_Native.Some (x,e) ->
                           let uu____4551 =
                             let uu____4552 = FStar_Syntax_Subst.compress x
                                in
                             uu____4552.FStar_Syntax_Syntax.n  in
                           (match uu____4551 with
                            | FStar_Syntax_Syntax.Tm_name x1 ->
                                let s = [FStar_Syntax_Syntax.NT (x1, e)]  in
                                let s1 bv1 =
                                  let uu___90_4565 = bv1  in
                                  let uu____4566 =
                                    FStar_Syntax_Subst.subst s
                                      bv1.FStar_Syntax_Syntax.sort
                                     in
                                  {
                                    FStar_Syntax_Syntax.ppname =
                                      (uu___90_4565.FStar_Syntax_Syntax.ppname);
                                    FStar_Syntax_Syntax.index =
                                      (uu___90_4565.FStar_Syntax_Syntax.index);
                                    FStar_Syntax_Syntax.sort = uu____4566
                                  }  in
                                let bvs1 = FStar_List.map s1 bvs  in
                                let uu____4572 =
                                  let uu___91_4573 = goal  in
                                  let uu____4574 = push_bvs e0 (bv :: bvs1)
                                     in
                                  let uu____4575 =
                                    FStar_Syntax_Subst.subst s
                                      goal.FStar_Tactics_Types.witness
                                     in
                                  let uu____4576 =
                                    FStar_Syntax_Subst.subst s
                                      goal.FStar_Tactics_Types.goal_ty
                                     in
                                  {
                                    FStar_Tactics_Types.context = uu____4574;
                                    FStar_Tactics_Types.witness = uu____4575;
                                    FStar_Tactics_Types.goal_ty = uu____4576;
                                    FStar_Tactics_Types.opts =
                                      (uu___91_4573.FStar_Tactics_Types.opts);
                                    FStar_Tactics_Types.is_guard =
                                      (uu___91_4573.FStar_Tactics_Types.is_guard)
                                  }  in
                                replace_cur uu____4572
                            | uu____4577 ->
                                fail
                                  "rewrite: Not an equality hypothesis with a variable on the LHS")
                       | uu____4578 ->
                           fail "rewrite: Not an equality hypothesis")))
  
let (rename_to :
  FStar_Syntax_Syntax.binder -> Prims.string -> Prims.unit tac) =
  fun b  ->
    fun s  ->
      bind cur_goal
        (fun goal  ->
           let uu____4603 = b  in
           match uu____4603 with
           | (bv,uu____4607) ->
               let bv' =
                 FStar_Syntax_Syntax.freshen_bv
                   (let uu___92_4611 = bv  in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (FStar_Ident.mk_ident
                           (s,
                             ((bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange)));
                      FStar_Syntax_Syntax.index =
                        (uu___92_4611.FStar_Syntax_Syntax.index);
                      FStar_Syntax_Syntax.sort =
                        (uu___92_4611.FStar_Syntax_Syntax.sort)
                    })
                  in
               let s1 =
                 let uu____4615 =
                   let uu____4616 =
                     let uu____4623 = FStar_Syntax_Syntax.bv_to_name bv'  in
                     (bv, uu____4623)  in
                   FStar_Syntax_Syntax.NT uu____4616  in
                 [uu____4615]  in
               let uu____4624 = subst_goal bv bv' s1 goal  in
               (match uu____4624 with
                | FStar_Pervasives_Native.None  ->
                    fail "rename_to: binder not found in environment"
                | FStar_Pervasives_Native.Some goal1 -> replace_cur goal1))
  
let (binder_retype : FStar_Syntax_Syntax.binder -> Prims.unit tac) =
  fun b  ->
    bind cur_goal
      (fun goal  ->
         let uu____4643 = b  in
         match uu____4643 with
         | (bv,uu____4647) ->
             let uu____4648 = split_env bv goal.FStar_Tactics_Types.context
                in
             (match uu____4648 with
              | FStar_Pervasives_Native.None  ->
                  fail "binder_retype: binder is not present in environment"
              | FStar_Pervasives_Native.Some (e0,bvs) ->
                  let uu____4677 = FStar_Syntax_Util.type_u ()  in
                  (match uu____4677 with
                   | (ty,u) ->
                       let uu____4686 = new_uvar "binder_retype" e0 ty  in
                       bind uu____4686
                         (fun t'  ->
                            let bv'' =
                              let uu___93_4696 = bv  in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___93_4696.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___93_4696.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = t'
                              }  in
                            let s =
                              let uu____4700 =
                                let uu____4701 =
                                  let uu____4708 =
                                    FStar_Syntax_Syntax.bv_to_name bv''  in
                                  (bv, uu____4708)  in
                                FStar_Syntax_Syntax.NT uu____4701  in
                              [uu____4700]  in
                            let bvs1 =
                              FStar_List.map
                                (fun b1  ->
                                   let uu___94_4716 = b1  in
                                   let uu____4717 =
                                     FStar_Syntax_Subst.subst s
                                       b1.FStar_Syntax_Syntax.sort
                                      in
                                   {
                                     FStar_Syntax_Syntax.ppname =
                                       (uu___94_4716.FStar_Syntax_Syntax.ppname);
                                     FStar_Syntax_Syntax.index =
                                       (uu___94_4716.FStar_Syntax_Syntax.index);
                                     FStar_Syntax_Syntax.sort = uu____4717
                                   }) bvs
                               in
                            let env' = push_bvs e0 (bv'' :: bvs1)  in
                            bind dismiss
                              (fun uu____4723  ->
                                 let uu____4724 =
                                   let uu____4727 =
                                     let uu____4730 =
                                       let uu___95_4731 = goal  in
                                       let uu____4732 =
                                         FStar_Syntax_Subst.subst s
                                           goal.FStar_Tactics_Types.witness
                                          in
                                       let uu____4733 =
                                         FStar_Syntax_Subst.subst s
                                           goal.FStar_Tactics_Types.goal_ty
                                          in
                                       {
                                         FStar_Tactics_Types.context = env';
                                         FStar_Tactics_Types.witness =
                                           uu____4732;
                                         FStar_Tactics_Types.goal_ty =
                                           uu____4733;
                                         FStar_Tactics_Types.opts =
                                           (uu___95_4731.FStar_Tactics_Types.opts);
                                         FStar_Tactics_Types.is_guard =
                                           (uu___95_4731.FStar_Tactics_Types.is_guard)
                                       }  in
                                     [uu____4730]  in
                                   add_goals uu____4727  in
                                 bind uu____4724
                                   (fun uu____4736  ->
                                      let uu____4737 =
                                        FStar_Syntax_Util.mk_eq2
                                          (FStar_Syntax_Syntax.U_succ u) ty
                                          bv.FStar_Syntax_Syntax.sort t'
                                         in
                                      add_irrelevant_goal
                                        "binder_retype equation" e0
                                        uu____4737
                                        goal.FStar_Tactics_Types.opts))))))
  
let (norm_binder_type :
  FStar_Syntax_Embeddings.norm_step Prims.list ->
    FStar_Syntax_Syntax.binder -> Prims.unit tac)
  =
  fun s  ->
    fun b  ->
      bind cur_goal
        (fun goal  ->
           let uu____4758 = b  in
           match uu____4758 with
           | (bv,uu____4762) ->
               let uu____4763 = split_env bv goal.FStar_Tactics_Types.context
                  in
               (match uu____4763 with
                | FStar_Pervasives_Native.None  ->
                    fail
                      "binder_retype: binder is not present in environment"
                | FStar_Pervasives_Native.Some (e0,bvs) ->
                    let steps =
                      let uu____4795 =
                        FStar_TypeChecker_Normalize.tr_norm_steps s  in
                      FStar_List.append
                        [FStar_TypeChecker_Normalize.Reify;
                        FStar_TypeChecker_Normalize.UnfoldTac] uu____4795
                       in
                    let sort' =
                      normalize steps e0 bv.FStar_Syntax_Syntax.sort  in
                    let bv' =
                      let uu___96_4800 = bv  in
                      {
                        FStar_Syntax_Syntax.ppname =
                          (uu___96_4800.FStar_Syntax_Syntax.ppname);
                        FStar_Syntax_Syntax.index =
                          (uu___96_4800.FStar_Syntax_Syntax.index);
                        FStar_Syntax_Syntax.sort = sort'
                      }  in
                    let env' = push_bvs e0 (bv' :: bvs)  in
                    replace_cur
                      (let uu___97_4804 = goal  in
                       {
                         FStar_Tactics_Types.context = env';
                         FStar_Tactics_Types.witness =
                           (uu___97_4804.FStar_Tactics_Types.witness);
                         FStar_Tactics_Types.goal_ty =
                           (uu___97_4804.FStar_Tactics_Types.goal_ty);
                         FStar_Tactics_Types.opts =
                           (uu___97_4804.FStar_Tactics_Types.opts);
                         FStar_Tactics_Types.is_guard =
                           (uu___97_4804.FStar_Tactics_Types.is_guard)
                       })))
  
let (revert : Prims.unit tac) =
  bind cur_goal
    (fun goal  ->
       let uu____4812 =
         FStar_TypeChecker_Env.pop_bv goal.FStar_Tactics_Types.context  in
       match uu____4812 with
       | FStar_Pervasives_Native.None  -> fail "Cannot revert; empty context"
       | FStar_Pervasives_Native.Some (x,env') ->
           let typ' =
             let uu____4834 =
               FStar_Syntax_Syntax.mk_Total goal.FStar_Tactics_Types.goal_ty
                in
             FStar_Syntax_Util.arrow [(x, FStar_Pervasives_Native.None)]
               uu____4834
              in
           let w' =
             FStar_Syntax_Util.abs [(x, FStar_Pervasives_Native.None)]
               goal.FStar_Tactics_Types.witness FStar_Pervasives_Native.None
              in
           replace_cur
             (let uu___98_4868 = goal  in
              {
                FStar_Tactics_Types.context = env';
                FStar_Tactics_Types.witness = w';
                FStar_Tactics_Types.goal_ty = typ';
                FStar_Tactics_Types.opts =
                  (uu___98_4868.FStar_Tactics_Types.opts);
                FStar_Tactics_Types.is_guard =
                  (uu___98_4868.FStar_Tactics_Types.is_guard)
              }))
  
let (free_in :
  FStar_Syntax_Syntax.bv -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun bv  ->
    fun t  ->
      let uu____4875 = FStar_Syntax_Free.names t  in
      FStar_Util.set_mem bv uu____4875
  
let rec (clear : FStar_Syntax_Syntax.binder -> Prims.unit tac) =
  fun b  ->
    let bv = FStar_Pervasives_Native.fst b  in
    bind cur_goal
      (fun goal  ->
         mlog
           (fun uu____4891  ->
              let uu____4892 = FStar_Syntax_Print.binder_to_string b  in
              let uu____4893 =
                let uu____4894 =
                  let uu____4895 =
                    FStar_TypeChecker_Env.all_binders
                      goal.FStar_Tactics_Types.context
                     in
                  FStar_All.pipe_right uu____4895 FStar_List.length  in
                FStar_All.pipe_right uu____4894 FStar_Util.string_of_int  in
              FStar_Util.print2 "Clear of (%s), env has %s binders\n"
                uu____4892 uu____4893)
           (fun uu____4906  ->
              let uu____4907 = split_env bv goal.FStar_Tactics_Types.context
                 in
              match uu____4907 with
              | FStar_Pervasives_Native.None  ->
                  fail "Cannot clear; binder not in environment"
              | FStar_Pervasives_Native.Some (e',bvs) ->
                  let rec check bvs1 =
                    match bvs1 with
                    | [] -> ret ()
                    | bv'::bvs2 ->
                        let uu____4952 =
                          free_in bv bv'.FStar_Syntax_Syntax.sort  in
                        if uu____4952
                        then
                          let uu____4955 =
                            let uu____4956 =
                              FStar_Syntax_Print.bv_to_string bv'  in
                            FStar_Util.format1
                              "Cannot clear; binder present in the type of %s"
                              uu____4956
                             in
                          fail uu____4955
                        else check bvs2
                     in
                  let uu____4958 =
                    free_in bv goal.FStar_Tactics_Types.goal_ty  in
                  if uu____4958
                  then fail "Cannot clear; binder present in goal"
                  else
                    (let uu____4962 = check bvs  in
                     bind uu____4962
                       (fun uu____4968  ->
                          let env' = push_bvs e' bvs  in
                          let uu____4970 =
                            new_uvar "clear.witness" env'
                              goal.FStar_Tactics_Types.goal_ty
                             in
                          bind uu____4970
                            (fun ut  ->
                               let uu____4976 =
                                 do_unify goal.FStar_Tactics_Types.context
                                   goal.FStar_Tactics_Types.witness ut
                                  in
                               if uu____4976
                               then
                                 replace_cur
                                   (let uu___99_4981 = goal  in
                                    {
                                      FStar_Tactics_Types.context = env';
                                      FStar_Tactics_Types.witness = ut;
                                      FStar_Tactics_Types.goal_ty =
                                        (uu___99_4981.FStar_Tactics_Types.goal_ty);
                                      FStar_Tactics_Types.opts =
                                        (uu___99_4981.FStar_Tactics_Types.opts);
                                      FStar_Tactics_Types.is_guard =
                                        (uu___99_4981.FStar_Tactics_Types.is_guard)
                                    })
                               else
                                 fail
                                   "Cannot clear; binder appears in witness")))))
  
let (clear_top : Prims.unit tac) =
  bind cur_goal
    (fun goal  ->
       let uu____4990 =
         FStar_TypeChecker_Env.pop_bv goal.FStar_Tactics_Types.context  in
       match uu____4990 with
       | FStar_Pervasives_Native.None  -> fail "Cannot clear; empty context"
       | FStar_Pervasives_Native.Some (x,uu____5004) ->
           let uu____5009 = FStar_Syntax_Syntax.mk_binder x  in
           clear uu____5009)
  
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
           let uu___100_5025 = g  in
           {
             FStar_Tactics_Types.context = ctx';
             FStar_Tactics_Types.witness =
               (uu___100_5025.FStar_Tactics_Types.witness);
             FStar_Tactics_Types.goal_ty =
               (uu___100_5025.FStar_Tactics_Types.goal_ty);
             FStar_Tactics_Types.opts =
               (uu___100_5025.FStar_Tactics_Types.opts);
             FStar_Tactics_Types.is_guard =
               (uu___100_5025.FStar_Tactics_Types.is_guard)
           }  in
         bind dismiss (fun uu____5027  -> add_goals [g']))
  
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
           let uu___101_5043 = g  in
           {
             FStar_Tactics_Types.context = ctx';
             FStar_Tactics_Types.witness =
               (uu___101_5043.FStar_Tactics_Types.witness);
             FStar_Tactics_Types.goal_ty =
               (uu___101_5043.FStar_Tactics_Types.goal_ty);
             FStar_Tactics_Types.opts =
               (uu___101_5043.FStar_Tactics_Types.opts);
             FStar_Tactics_Types.is_guard =
               (uu___101_5043.FStar_Tactics_Types.is_guard)
           }  in
         bind dismiss (fun uu____5045  -> add_goals [g']))
  
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
            let uu____5077 = FStar_Syntax_Subst.compress t  in
            uu____5077.FStar_Syntax_Syntax.n  in
          let uu____5080 =
            if d = FStar_Tactics_Types.TopDown
            then
              f env
                (let uu___103_5086 = t  in
                 {
                   FStar_Syntax_Syntax.n = tn;
                   FStar_Syntax_Syntax.pos =
                     (uu___103_5086.FStar_Syntax_Syntax.pos);
                   FStar_Syntax_Syntax.vars =
                     (uu___103_5086.FStar_Syntax_Syntax.vars)
                 })
            else ret t  in
          bind uu____5080
            (fun t1  ->
               let tn1 =
                 let uu____5094 =
                   let uu____5095 = FStar_Syntax_Subst.compress t1  in
                   uu____5095.FStar_Syntax_Syntax.n  in
                 match uu____5094 with
                 | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
                     let ff = tac_fold_env d f env  in
                     let uu____5127 = ff hd1  in
                     bind uu____5127
                       (fun hd2  ->
                          let fa uu____5147 =
                            match uu____5147 with
                            | (a,q) ->
                                let uu____5160 = ff a  in
                                bind uu____5160 (fun a1  -> ret (a1, q))
                             in
                          let uu____5173 = mapM fa args  in
                          bind uu____5173
                            (fun args1  ->
                               ret (FStar_Syntax_Syntax.Tm_app (hd2, args1))))
                 | FStar_Syntax_Syntax.Tm_abs (bs,t2,k) ->
                     let uu____5233 = FStar_Syntax_Subst.open_term bs t2  in
                     (match uu____5233 with
                      | (bs1,t') ->
                          let uu____5242 =
                            let uu____5245 =
                              FStar_TypeChecker_Env.push_binders env bs1  in
                            tac_fold_env d f uu____5245 t'  in
                          bind uu____5242
                            (fun t''  ->
                               let uu____5249 =
                                 let uu____5250 =
                                   let uu____5267 =
                                     FStar_Syntax_Subst.close_binders bs1  in
                                   let uu____5268 =
                                     FStar_Syntax_Subst.close bs1 t''  in
                                   (uu____5267, uu____5268, k)  in
                                 FStar_Syntax_Syntax.Tm_abs uu____5250  in
                               ret uu____5249))
                 | FStar_Syntax_Syntax.Tm_arrow (bs,k) -> ret tn
                 | uu____5289 -> ret tn  in
               bind tn1
                 (fun tn2  ->
                    let t' =
                      let uu___102_5296 = t1  in
                      {
                        FStar_Syntax_Syntax.n = tn2;
                        FStar_Syntax_Syntax.pos =
                          (uu___102_5296.FStar_Syntax_Syntax.pos);
                        FStar_Syntax_Syntax.vars =
                          (uu___102_5296.FStar_Syntax_Syntax.vars)
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
            let uu____5325 = FStar_TypeChecker_TcTerm.tc_term env t  in
            match uu____5325 with
            | (t1,lcomp,g) ->
                let uu____5337 =
                  (let uu____5340 =
                     FStar_Syntax_Util.is_pure_or_ghost_lcomp lcomp  in
                   Prims.op_Negation uu____5340) ||
                    (let uu____5342 = FStar_TypeChecker_Rel.is_trivial g  in
                     Prims.op_Negation uu____5342)
                   in
                if uu____5337
                then ret t1
                else
                  (let rewrite_eq =
                     let typ = lcomp.FStar_Syntax_Syntax.res_typ  in
                     let uu____5352 = new_uvar "pointwise_rec" env typ  in
                     bind uu____5352
                       (fun ut  ->
                          log ps
                            (fun uu____5363  ->
                               let uu____5364 =
                                 FStar_Syntax_Print.term_to_string t1  in
                               let uu____5365 =
                                 FStar_Syntax_Print.term_to_string ut  in
                               FStar_Util.print2
                                 "Pointwise_rec: making equality\n\t%s ==\n\t%s\n"
                                 uu____5364 uu____5365);
                          (let uu____5366 =
                             let uu____5369 =
                               let uu____5370 =
                                 FStar_TypeChecker_TcTerm.universe_of env typ
                                  in
                               FStar_Syntax_Util.mk_eq2 uu____5370 typ t1 ut
                                in
                             add_irrelevant_goal "pointwise_rec equation" env
                               uu____5369 opts
                              in
                           bind uu____5366
                             (fun uu____5373  ->
                                let uu____5374 =
                                  bind tau
                                    (fun uu____5380  ->
                                       let ut1 =
                                         FStar_TypeChecker_Normalize.reduce_uvar_solutions
                                           env ut
                                          in
                                       log ps
                                         (fun uu____5386  ->
                                            let uu____5387 =
                                              FStar_Syntax_Print.term_to_string
                                                t1
                                               in
                                            let uu____5388 =
                                              FStar_Syntax_Print.term_to_string
                                                ut1
                                               in
                                            FStar_Util.print2
                                              "Pointwise_rec: succeeded rewriting\n\t%s to\n\t%s\n"
                                              uu____5387 uu____5388);
                                       ret ut1)
                                   in
                                focus uu____5374)))
                      in
                   let uu____5389 = trytac' rewrite_eq  in
                   bind uu____5389
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
           let uu____5431 =
             match ps.FStar_Tactics_Types.goals with
             | g::gs -> (g, gs)
             | [] -> failwith "Pointwise: no goals"  in
           match uu____5431 with
           | (g,gs) ->
               let gt1 = g.FStar_Tactics_Types.goal_ty  in
               (log ps
                  (fun uu____5468  ->
                     let uu____5469 = FStar_Syntax_Print.term_to_string gt1
                        in
                     FStar_Util.print1 "Pointwise starting with %s\n"
                       uu____5469);
                bind dismiss_all
                  (fun uu____5472  ->
                     let uu____5473 =
                       tac_fold_env d
                         (pointwise_rec ps tau g.FStar_Tactics_Types.opts)
                         g.FStar_Tactics_Types.context gt1
                        in
                     bind uu____5473
                       (fun gt'  ->
                          log ps
                            (fun uu____5483  ->
                               let uu____5484 =
                                 FStar_Syntax_Print.term_to_string gt'  in
                               FStar_Util.print1
                                 "Pointwise seems to have succeded with %s\n"
                                 uu____5484);
                          (let uu____5485 = push_goals gs  in
                           bind uu____5485
                             (fun uu____5489  ->
                                add_goals
                                  [(let uu___104_5491 = g  in
                                    {
                                      FStar_Tactics_Types.context =
                                        (uu___104_5491.FStar_Tactics_Types.context);
                                      FStar_Tactics_Types.witness =
                                        (uu___104_5491.FStar_Tactics_Types.witness);
                                      FStar_Tactics_Types.goal_ty = gt';
                                      FStar_Tactics_Types.opts =
                                        (uu___104_5491.FStar_Tactics_Types.opts);
                                      FStar_Tactics_Types.is_guard =
                                        (uu___104_5491.FStar_Tactics_Types.is_guard)
                                    })]))))))
  
let (trefl : Prims.unit tac) =
  bind cur_goal
    (fun g  ->
       let uu____5513 =
         FStar_Syntax_Util.un_squash g.FStar_Tactics_Types.goal_ty  in
       match uu____5513 with
       | FStar_Pervasives_Native.Some t ->
           let uu____5525 = FStar_Syntax_Util.head_and_args' t  in
           (match uu____5525 with
            | (hd1,args) ->
                let uu____5558 =
                  let uu____5571 =
                    let uu____5572 = FStar_Syntax_Util.un_uinst hd1  in
                    uu____5572.FStar_Syntax_Syntax.n  in
                  (uu____5571, args)  in
                (match uu____5558 with
                 | (FStar_Syntax_Syntax.Tm_fvar
                    fv,uu____5586::(l,uu____5588)::(r,uu____5590)::[]) when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.eq2_lid
                     ->
                     let uu____5637 =
                       let uu____5638 =
                         do_unify g.FStar_Tactics_Types.context l r  in
                       Prims.op_Negation uu____5638  in
                     if uu____5637
                     then
                       let uu____5641 = tts g.FStar_Tactics_Types.context l
                          in
                       let uu____5642 = tts g.FStar_Tactics_Types.context r
                          in
                       fail2 "trefl: not a trivial equality (%s vs %s)"
                         uu____5641 uu____5642
                     else solve g FStar_Syntax_Util.exp_unit
                 | (hd2,uu____5645) ->
                     let uu____5662 = tts g.FStar_Tactics_Types.context t  in
                     fail1 "trefl: not an equality (%s)" uu____5662))
       | FStar_Pervasives_Native.None  -> fail "not an irrelevant goal")
  
let (dup : Prims.unit tac) =
  bind cur_goal
    (fun g  ->
       let uu____5672 =
         new_uvar "dup" g.FStar_Tactics_Types.context
           g.FStar_Tactics_Types.goal_ty
          in
       bind uu____5672
         (fun u  ->
            let g' =
              let uu___105_5679 = g  in
              {
                FStar_Tactics_Types.context =
                  (uu___105_5679.FStar_Tactics_Types.context);
                FStar_Tactics_Types.witness = u;
                FStar_Tactics_Types.goal_ty =
                  (uu___105_5679.FStar_Tactics_Types.goal_ty);
                FStar_Tactics_Types.opts =
                  (uu___105_5679.FStar_Tactics_Types.opts);
                FStar_Tactics_Types.is_guard =
                  (uu___105_5679.FStar_Tactics_Types.is_guard)
              }  in
            bind dismiss
              (fun uu____5682  ->
                 let uu____5683 =
                   let uu____5686 =
                     let uu____5687 =
                       FStar_TypeChecker_TcTerm.universe_of
                         g.FStar_Tactics_Types.context
                         g.FStar_Tactics_Types.goal_ty
                        in
                     FStar_Syntax_Util.mk_eq2 uu____5687
                       g.FStar_Tactics_Types.goal_ty u
                       g.FStar_Tactics_Types.witness
                      in
                   add_irrelevant_goal "dup equation"
                     g.FStar_Tactics_Types.context uu____5686
                     g.FStar_Tactics_Types.opts
                    in
                 bind uu____5683
                   (fun uu____5690  ->
                      let uu____5691 = add_goals [g']  in
                      bind uu____5691 (fun uu____5695  -> ret ())))))
  
let (flip : Prims.unit tac) =
  bind get
    (fun ps  ->
       match ps.FStar_Tactics_Types.goals with
       | g1::g2::gs ->
           set
             (let uu___106_5714 = ps  in
              {
                FStar_Tactics_Types.main_context =
                  (uu___106_5714.FStar_Tactics_Types.main_context);
                FStar_Tactics_Types.main_goal =
                  (uu___106_5714.FStar_Tactics_Types.main_goal);
                FStar_Tactics_Types.all_implicits =
                  (uu___106_5714.FStar_Tactics_Types.all_implicits);
                FStar_Tactics_Types.goals = (g2 :: g1 :: gs);
                FStar_Tactics_Types.smt_goals =
                  (uu___106_5714.FStar_Tactics_Types.smt_goals);
                FStar_Tactics_Types.depth =
                  (uu___106_5714.FStar_Tactics_Types.depth);
                FStar_Tactics_Types.__dump =
                  (uu___106_5714.FStar_Tactics_Types.__dump);
                FStar_Tactics_Types.psc =
                  (uu___106_5714.FStar_Tactics_Types.psc);
                FStar_Tactics_Types.entry_range =
                  (uu___106_5714.FStar_Tactics_Types.entry_range)
              })
       | uu____5715 -> fail "flip: less than 2 goals")
  
let (later : Prims.unit tac) =
  bind get
    (fun ps  ->
       match ps.FStar_Tactics_Types.goals with
       | [] -> ret ()
       | g::gs ->
           set
             (let uu___107_5732 = ps  in
              {
                FStar_Tactics_Types.main_context =
                  (uu___107_5732.FStar_Tactics_Types.main_context);
                FStar_Tactics_Types.main_goal =
                  (uu___107_5732.FStar_Tactics_Types.main_goal);
                FStar_Tactics_Types.all_implicits =
                  (uu___107_5732.FStar_Tactics_Types.all_implicits);
                FStar_Tactics_Types.goals = (FStar_List.append gs [g]);
                FStar_Tactics_Types.smt_goals =
                  (uu___107_5732.FStar_Tactics_Types.smt_goals);
                FStar_Tactics_Types.depth =
                  (uu___107_5732.FStar_Tactics_Types.depth);
                FStar_Tactics_Types.__dump =
                  (uu___107_5732.FStar_Tactics_Types.__dump);
                FStar_Tactics_Types.psc =
                  (uu___107_5732.FStar_Tactics_Types.psc);
                FStar_Tactics_Types.entry_range =
                  (uu___107_5732.FStar_Tactics_Types.entry_range)
              }))
  
let (qed : Prims.unit tac) =
  bind get
    (fun ps  ->
       match ps.FStar_Tactics_Types.goals with
       | [] -> ret ()
       | uu____5741 -> fail "Not done!")
  
let (cases :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 tac)
  =
  fun t  ->
    let uu____5759 =
      bind cur_goal
        (fun g  ->
           let uu____5773 = __tc g.FStar_Tactics_Types.context t  in
           bind uu____5773
             (fun uu____5809  ->
                match uu____5809 with
                | (t1,typ,guard) ->
                    let uu____5825 = FStar_Syntax_Util.head_and_args typ  in
                    (match uu____5825 with
                     | (hd1,args) ->
                         let uu____5868 =
                           let uu____5881 =
                             let uu____5882 = FStar_Syntax_Util.un_uinst hd1
                                in
                             uu____5882.FStar_Syntax_Syntax.n  in
                           (uu____5881, args)  in
                         (match uu____5868 with
                          | (FStar_Syntax_Syntax.Tm_fvar
                             fv,(p,uu____5901)::(q,uu____5903)::[]) when
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
                                let uu___108_5941 = g  in
                                let uu____5942 =
                                  FStar_TypeChecker_Env.push_bv
                                    g.FStar_Tactics_Types.context v_p
                                   in
                                {
                                  FStar_Tactics_Types.context = uu____5942;
                                  FStar_Tactics_Types.witness =
                                    (uu___108_5941.FStar_Tactics_Types.witness);
                                  FStar_Tactics_Types.goal_ty =
                                    (uu___108_5941.FStar_Tactics_Types.goal_ty);
                                  FStar_Tactics_Types.opts =
                                    (uu___108_5941.FStar_Tactics_Types.opts);
                                  FStar_Tactics_Types.is_guard =
                                    (uu___108_5941.FStar_Tactics_Types.is_guard)
                                }  in
                              let g2 =
                                let uu___109_5944 = g  in
                                let uu____5945 =
                                  FStar_TypeChecker_Env.push_bv
                                    g.FStar_Tactics_Types.context v_q
                                   in
                                {
                                  FStar_Tactics_Types.context = uu____5945;
                                  FStar_Tactics_Types.witness =
                                    (uu___109_5944.FStar_Tactics_Types.witness);
                                  FStar_Tactics_Types.goal_ty =
                                    (uu___109_5944.FStar_Tactics_Types.goal_ty);
                                  FStar_Tactics_Types.opts =
                                    (uu___109_5944.FStar_Tactics_Types.opts);
                                  FStar_Tactics_Types.is_guard =
                                    (uu___109_5944.FStar_Tactics_Types.is_guard)
                                }  in
                              bind dismiss
                                (fun uu____5952  ->
                                   let uu____5953 = add_goals [g1; g2]  in
                                   bind uu____5953
                                     (fun uu____5962  ->
                                        let uu____5963 =
                                          let uu____5968 =
                                            FStar_Syntax_Syntax.bv_to_name
                                              v_p
                                             in
                                          let uu____5969 =
                                            FStar_Syntax_Syntax.bv_to_name
                                              v_q
                                             in
                                          (uu____5968, uu____5969)  in
                                        ret uu____5963))
                          | uu____5974 ->
                              let uu____5987 =
                                tts g.FStar_Tactics_Types.context typ  in
                              fail1 "Not a disjunction: %s" uu____5987))))
       in
    FStar_All.pipe_left (wrap_err "cases") uu____5759
  
let (set_options : Prims.string -> Prims.unit tac) =
  fun s  ->
    bind cur_goal
      (fun g  ->
         FStar_Options.push ();
         (let uu____6025 = FStar_Util.smap_copy g.FStar_Tactics_Types.opts
             in
          FStar_Options.set uu____6025);
         (let res = FStar_Options.set_options FStar_Options.Set s  in
          let opts' = FStar_Options.peek ()  in
          FStar_Options.pop ();
          (match res with
           | FStar_Getopt.Success  ->
               let g' =
                 let uu___110_6032 = g  in
                 {
                   FStar_Tactics_Types.context =
                     (uu___110_6032.FStar_Tactics_Types.context);
                   FStar_Tactics_Types.witness =
                     (uu___110_6032.FStar_Tactics_Types.witness);
                   FStar_Tactics_Types.goal_ty =
                     (uu___110_6032.FStar_Tactics_Types.goal_ty);
                   FStar_Tactics_Types.opts = opts';
                   FStar_Tactics_Types.is_guard =
                     (uu___110_6032.FStar_Tactics_Types.is_guard)
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
      let uu____6076 =
        bind cur_goal
          (fun goal  ->
             let env =
               FStar_TypeChecker_Env.set_expected_typ
                 goal.FStar_Tactics_Types.context ty
                in
             let uu____6084 = __tc env tm  in
             bind uu____6084
               (fun uu____6104  ->
                  match uu____6104 with
                  | (tm1,typ,guard) ->
                      (FStar_TypeChecker_Rel.force_trivial_guard env guard;
                       ret tm1)))
         in
      FStar_All.pipe_left (wrap_err "unquote") uu____6076
  
let (uvar_env :
  env ->
    FStar_Syntax_Syntax.typ FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.term tac)
  =
  fun env  ->
    fun ty  ->
      let uu____6135 =
        match ty with
        | FStar_Pervasives_Native.Some ty1 -> ret ty1
        | FStar_Pervasives_Native.None  ->
            let uu____6141 =
              let uu____6142 = FStar_Syntax_Util.type_u ()  in
              FStar_All.pipe_left FStar_Pervasives_Native.fst uu____6142  in
            new_uvar "uvar_env.2" env uu____6141
         in
      bind uu____6135
        (fun typ  ->
           let uu____6154 = new_uvar "uvar_env" env typ  in
           bind uu____6154 (fun t  -> ret t))
  
let (unshelve : FStar_Syntax_Syntax.term -> Prims.unit tac) =
  fun t  ->
    let uu____6166 =
      bind cur_goal
        (fun goal  ->
           let uu____6172 = __tc goal.FStar_Tactics_Types.context t  in
           bind uu____6172
             (fun uu____6192  ->
                match uu____6192 with
                | (t1,typ,guard) ->
                    let uu____6204 =
                      must_trivial goal.FStar_Tactics_Types.context guard  in
                    bind uu____6204
                      (fun uu____6209  ->
                         let uu____6210 =
                           let uu____6213 =
                             let uu___111_6214 = goal  in
                             let uu____6215 =
                               bnorm goal.FStar_Tactics_Types.context t1  in
                             let uu____6216 =
                               bnorm goal.FStar_Tactics_Types.context typ  in
                             {
                               FStar_Tactics_Types.context =
                                 (uu___111_6214.FStar_Tactics_Types.context);
                               FStar_Tactics_Types.witness = uu____6215;
                               FStar_Tactics_Types.goal_ty = uu____6216;
                               FStar_Tactics_Types.opts =
                                 (uu___111_6214.FStar_Tactics_Types.opts);
                               FStar_Tactics_Types.is_guard = false
                             }  in
                           [uu____6213]  in
                         add_goals uu____6210)))
       in
    FStar_All.pipe_left (wrap_err "unshelve") uu____6166
  
let (unify :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool tac) =
  fun t1  ->
    fun t2  ->
      bind get
        (fun ps  ->
           let uu____6234 =
             do_unify ps.FStar_Tactics_Types.main_context t1 t2  in
           ret uu____6234)
  
let (launch_process :
  Prims.string -> Prims.string -> Prims.string -> Prims.string tac) =
  fun prog  ->
    fun args  ->
      fun input  ->
        bind idtac
          (fun uu____6251  ->
             let uu____6252 = FStar_Options.unsafe_tactic_exec ()  in
             if uu____6252
             then
               let s =
                 FStar_Util.launch_process true "tactic_launch" prog args
                   input (fun uu____6258  -> fun uu____6259  -> false)
                  in
               ret s
             else
               fail
                 "launch_process: will not run anything unless --unsafe_tactic_exec is provided")
  
let (goal_of_goal_ty :
  env ->
    FStar_Syntax_Syntax.typ ->
      (FStar_Tactics_Types.goal,FStar_TypeChecker_Env.guard_t)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun typ  ->
      let uu____6275 =
        FStar_TypeChecker_Util.new_implicit_var "proofstate_of_goal_ty"
          typ.FStar_Syntax_Syntax.pos env typ
         in
      match uu____6275 with
      | (u,uu____6293,g_u) ->
          let g =
            let uu____6308 = FStar_Options.peek ()  in
            {
              FStar_Tactics_Types.context = env;
              FStar_Tactics_Types.witness = u;
              FStar_Tactics_Types.goal_ty = typ;
              FStar_Tactics_Types.opts = uu____6308;
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
      let uu____6319 = goal_of_goal_ty env typ  in
      match uu____6319 with
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
  