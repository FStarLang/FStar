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
      let uu____531 = FStar_ST.op_Bang tac_verb_dbg  in
      match uu____531 with
      | FStar_Pervasives_Native.None  ->
          ((let uu____558 =
              let uu____561 =
                FStar_TypeChecker_Env.debug
                  ps.FStar_Tactics_Types.main_context
                  (FStar_Options.Other "TacVerbose")
                 in
              FStar_Pervasives_Native.Some uu____561  in
            FStar_ST.op_Colon_Equals tac_verb_dbg uu____558);
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
         (let uu____630 =
            FStar_TypeChecker_Env.debug ps.FStar_Tactics_Types.main_context
              (FStar_Options.Other "TacFail")
             in
          if uu____630
          then dump_proofstate ps (Prims.strcat "TACTING FAILING: " msg)
          else ());
         FStar_Tactics_Result.Failed (msg, ps))
  
let fail1 : 'Auu____635 . Prims.string -> Prims.string -> 'Auu____635 tac =
  fun msg  ->
    fun x  -> let uu____646 = FStar_Util.format1 msg x  in fail uu____646
  
let fail2 :
  'Auu____651 .
    Prims.string -> Prims.string -> Prims.string -> 'Auu____651 tac
  =
  fun msg  ->
    fun x  ->
      fun y  -> let uu____666 = FStar_Util.format2 msg x y  in fail uu____666
  
let fail3 :
  'Auu____672 .
    Prims.string ->
      Prims.string -> Prims.string -> Prims.string -> 'Auu____672 tac
  =
  fun msg  ->
    fun x  ->
      fun y  ->
        fun z  ->
          let uu____691 = FStar_Util.format3 msg x y z  in fail uu____691
  
let fail4 :
  'Auu____698 .
    Prims.string ->
      Prims.string ->
        Prims.string -> Prims.string -> Prims.string -> 'Auu____698 tac
  =
  fun msg  ->
    fun x  ->
      fun y  ->
        fun z  ->
          fun w  ->
            let uu____721 = FStar_Util.format4 msg x y z w  in fail uu____721
  
let trytac' : 'a . 'a tac -> (Prims.string,'a) FStar_Util.either tac =
  fun t  ->
    mk_tac
      (fun ps  ->
         let tx = FStar_Syntax_Unionfind.new_transaction ()  in
         let uu____751 = run t ps  in
         match uu____751 with
         | FStar_Tactics_Result.Success (a,q) ->
             (FStar_Syntax_Unionfind.commit tx;
              FStar_Tactics_Result.Success ((FStar_Util.Inr a), q))
         | FStar_Tactics_Result.Failed (m,uu____772) ->
             (FStar_Syntax_Unionfind.rollback tx;
              FStar_Tactics_Result.Success ((FStar_Util.Inl m), ps)))
  
let trytac : 'a . 'a tac -> 'a FStar_Pervasives_Native.option tac =
  fun t  ->
    let uu____797 = trytac' t  in
    bind uu____797
      (fun r  ->
         match r with
         | FStar_Util.Inr v1 -> ret (FStar_Pervasives_Native.Some v1)
         | FStar_Util.Inl uu____824 -> ret FStar_Pervasives_Native.None)
  
let wrap_err : 'a . Prims.string -> 'a tac -> 'a tac =
  fun pref  ->
    fun t  ->
      mk_tac
        (fun ps  ->
           let uu____850 = run t ps  in
           match uu____850 with
           | FStar_Tactics_Result.Success (a,q) ->
               FStar_Tactics_Result.Success (a, q)
           | FStar_Tactics_Result.Failed (msg,q) ->
               FStar_Tactics_Result.Failed
                 ((Prims.strcat pref (Prims.strcat ": " msg)), q))
  
let (set : FStar_Tactics_Types.proofstate -> Prims.unit tac) =
  fun p  -> mk_tac (fun uu____867  -> FStar_Tactics_Result.Success ((), p)) 
let (do_unify :
  env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let debug_on uu____880 =
          let uu____881 =
            FStar_Options.set_options FStar_Options.Set
              "--debug_level Rel --debug_level RelCheck"
             in
          ()  in
        let debug_off uu____885 =
          let uu____886 = FStar_Options.set_options FStar_Options.Reset ""
             in
          ()  in
        (let uu____888 =
           FStar_TypeChecker_Env.debug env (FStar_Options.Other "1346")  in
         if uu____888
         then
           (debug_on ();
            (let uu____890 = FStar_Syntax_Print.term_to_string t1  in
             let uu____891 = FStar_Syntax_Print.term_to_string t2  in
             FStar_Util.print2 "%%%%%%%%do_unify %s =? %s\n" uu____890
               uu____891))
         else ());
        (try
           let res = FStar_TypeChecker_Rel.teq_nosmt env t1 t2  in
           debug_off (); res
         with | uu____903 -> (debug_off (); false))
  
let (trysolve :
  FStar_Tactics_Types.goal -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun goal  ->
    fun solution  ->
      do_unify goal.FStar_Tactics_Types.context solution
        goal.FStar_Tactics_Types.witness
  
let (dismiss : Prims.unit tac) =
  bind get
    (fun p  ->
       let uu____916 =
         let uu___61_917 = p  in
         let uu____918 = FStar_List.tl p.FStar_Tactics_Types.goals  in
         {
           FStar_Tactics_Types.main_context =
             (uu___61_917.FStar_Tactics_Types.main_context);
           FStar_Tactics_Types.main_goal =
             (uu___61_917.FStar_Tactics_Types.main_goal);
           FStar_Tactics_Types.all_implicits =
             (uu___61_917.FStar_Tactics_Types.all_implicits);
           FStar_Tactics_Types.goals = uu____918;
           FStar_Tactics_Types.smt_goals =
             (uu___61_917.FStar_Tactics_Types.smt_goals);
           FStar_Tactics_Types.depth =
             (uu___61_917.FStar_Tactics_Types.depth);
           FStar_Tactics_Types.__dump =
             (uu___61_917.FStar_Tactics_Types.__dump);
           FStar_Tactics_Types.psc = (uu___61_917.FStar_Tactics_Types.psc);
           FStar_Tactics_Types.entry_range =
             (uu___61_917.FStar_Tactics_Types.entry_range)
         }  in
       set uu____916)
  
let (solve :
  FStar_Tactics_Types.goal -> FStar_Syntax_Syntax.term -> Prims.unit tac) =
  fun goal  ->
    fun solution  ->
      let uu____931 = trysolve goal solution  in
      if uu____931
      then dismiss
      else
        (let uu____935 =
           let uu____936 = tts goal.FStar_Tactics_Types.context solution  in
           let uu____937 =
             tts goal.FStar_Tactics_Types.context
               goal.FStar_Tactics_Types.witness
              in
           let uu____938 =
             tts goal.FStar_Tactics_Types.context
               goal.FStar_Tactics_Types.goal_ty
              in
           FStar_Util.format3 "%s does not solve %s : %s" uu____936 uu____937
             uu____938
            in
         fail uu____935)
  
let (dismiss_all : Prims.unit tac) =
  bind get
    (fun p  ->
       set
         (let uu___62_945 = p  in
          {
            FStar_Tactics_Types.main_context =
              (uu___62_945.FStar_Tactics_Types.main_context);
            FStar_Tactics_Types.main_goal =
              (uu___62_945.FStar_Tactics_Types.main_goal);
            FStar_Tactics_Types.all_implicits =
              (uu___62_945.FStar_Tactics_Types.all_implicits);
            FStar_Tactics_Types.goals = [];
            FStar_Tactics_Types.smt_goals =
              (uu___62_945.FStar_Tactics_Types.smt_goals);
            FStar_Tactics_Types.depth =
              (uu___62_945.FStar_Tactics_Types.depth);
            FStar_Tactics_Types.__dump =
              (uu___62_945.FStar_Tactics_Types.__dump);
            FStar_Tactics_Types.psc = (uu___62_945.FStar_Tactics_Types.psc);
            FStar_Tactics_Types.entry_range =
              (uu___62_945.FStar_Tactics_Types.entry_range)
          }))
  
let (nwarn : Prims.int FStar_ST.ref) =
  FStar_Util.mk_ref (Prims.parse_int "0") 
let (check_valid_goal : FStar_Tactics_Types.goal -> Prims.unit) =
  fun g  ->
    let uu____962 = FStar_Options.defensive ()  in
    if uu____962
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
        let uu____974 = FStar_TypeChecker_Env.pop_bv e  in
        match uu____974 with
        | FStar_Pervasives_Native.None  -> b3
        | FStar_Pervasives_Native.Some (bv,e1) ->
            let b4 =
              b3 &&
                (FStar_TypeChecker_Env.closed e1 bv.FStar_Syntax_Syntax.sort)
               in
            aux b4 e1
         in
      let uu____992 =
        (let uu____995 = aux b2 env  in Prims.op_Negation uu____995) &&
          (let uu____997 = FStar_ST.op_Bang nwarn  in
           uu____997 < (Prims.parse_int "5"))
         in
      (if uu____992
       then
         ((let uu____1018 =
             let uu____1023 =
               let uu____1024 = goal_to_string g  in
               FStar_Util.format1
                 "The following goal is ill-formed. Keeping calm and carrying on...\n<%s>\n\n"
                 uu____1024
                in
             (FStar_Errors.Warning_IllFormedGoal, uu____1023)  in
           FStar_Errors.log_issue
             (g.FStar_Tactics_Types.goal_ty).FStar_Syntax_Syntax.pos
             uu____1018);
          (let uu____1025 =
             let uu____1026 = FStar_ST.op_Bang nwarn  in
             uu____1026 + (Prims.parse_int "1")  in
           FStar_ST.op_Colon_Equals nwarn uu____1025))
       else ())
    else ()
  
let (add_goals : FStar_Tactics_Types.goal Prims.list -> Prims.unit tac) =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___63_1084 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___63_1084.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___63_1084.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___63_1084.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (FStar_List.append gs p.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___63_1084.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___63_1084.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___63_1084.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___63_1084.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___63_1084.FStar_Tactics_Types.entry_range)
            }))
  
let (add_smt_goals : FStar_Tactics_Types.goal Prims.list -> Prims.unit tac) =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___64_1102 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___64_1102.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___64_1102.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___64_1102.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___64_1102.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (FStar_List.append gs p.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___64_1102.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___64_1102.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___64_1102.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___64_1102.FStar_Tactics_Types.entry_range)
            }))
  
let (push_goals : FStar_Tactics_Types.goal Prims.list -> Prims.unit tac) =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___65_1120 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___65_1120.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___65_1120.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___65_1120.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (FStar_List.append p.FStar_Tactics_Types.goals gs);
              FStar_Tactics_Types.smt_goals =
                (uu___65_1120.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___65_1120.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___65_1120.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___65_1120.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___65_1120.FStar_Tactics_Types.entry_range)
            }))
  
let (push_smt_goals : FStar_Tactics_Types.goal Prims.list -> Prims.unit tac)
  =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___66_1138 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___66_1138.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___66_1138.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___66_1138.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___66_1138.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (FStar_List.append p.FStar_Tactics_Types.smt_goals gs);
              FStar_Tactics_Types.depth =
                (uu___66_1138.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___66_1138.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___66_1138.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___66_1138.FStar_Tactics_Types.entry_range)
            }))
  
let (replace_cur : FStar_Tactics_Types.goal -> Prims.unit tac) =
  fun g  -> bind dismiss (fun uu____1147  -> add_goals [g]) 
let (add_implicits : implicits -> Prims.unit tac) =
  fun i  ->
    bind get
      (fun p  ->
         set
           (let uu___67_1159 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___67_1159.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___67_1159.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (FStar_List.append i p.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___67_1159.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___67_1159.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___67_1159.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___67_1159.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___67_1159.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___67_1159.FStar_Tactics_Types.entry_range)
            }))
  
let (new_uvar :
  Prims.string ->
    env -> FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.term tac)
  =
  fun reason  ->
    fun env  ->
      fun typ  ->
        let uu____1185 =
          FStar_TypeChecker_Util.new_implicit_var reason
            typ.FStar_Syntax_Syntax.pos env typ
           in
        match uu____1185 with
        | (u,uu____1201,g_u) ->
            let uu____1215 =
              add_implicits g_u.FStar_TypeChecker_Env.implicits  in
            bind uu____1215 (fun uu____1219  -> ret u)
  
let (is_true : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____1223 = FStar_Syntax_Util.un_squash t  in
    match uu____1223 with
    | FStar_Pervasives_Native.Some t' ->
        let uu____1233 =
          let uu____1234 = FStar_Syntax_Subst.compress t'  in
          uu____1234.FStar_Syntax_Syntax.n  in
        (match uu____1233 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.true_lid
         | uu____1238 -> false)
    | uu____1239 -> false
  
let (is_false : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____1247 = FStar_Syntax_Util.un_squash t  in
    match uu____1247 with
    | FStar_Pervasives_Native.Some t' ->
        let uu____1257 =
          let uu____1258 = FStar_Syntax_Subst.compress t'  in
          uu____1258.FStar_Syntax_Syntax.n  in
        (match uu____1257 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.false_lid
         | uu____1262 -> false)
    | uu____1263 -> false
  
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
            let uu____1303 = env.FStar_TypeChecker_Env.universe_of env phi
               in
            FStar_Syntax_Util.mk_squash uu____1303 phi  in
          let uu____1304 = new_uvar reason env typ  in
          bind uu____1304
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
             let uu____1360 =
               (ps.FStar_Tactics_Types.main_context).FStar_TypeChecker_Env.type_of
                 e t
                in
             ret uu____1360
           with
           | ex ->
               let uu____1387 = tts e t  in
               let uu____1388 =
                 let uu____1389 = FStar_TypeChecker_Env.all_binders e  in
                 FStar_All.pipe_right uu____1389
                   (FStar_Syntax_Print.binders_to_string ", ")
                  in
               fail2 "Cannot type %s in context (%s)" uu____1387 uu____1388)
  
let (must_trivial : env -> FStar_TypeChecker_Env.guard_t -> Prims.unit tac) =
  fun e  ->
    fun g  ->
      try
        let uu____1413 =
          let uu____1414 =
            let uu____1415 = FStar_TypeChecker_Rel.discharge_guard_no_smt e g
               in
            FStar_All.pipe_left FStar_TypeChecker_Rel.is_trivial uu____1415
             in
          Prims.op_Negation uu____1414  in
        if uu____1413 then fail "got non-trivial guard" else ret ()
      with | uu____1424 -> fail "got non-trivial guard"
  
let (tc : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.typ tac) =
  fun t  ->
    let uu____1432 =
      bind cur_goal
        (fun goal  ->
           let uu____1438 = __tc goal.FStar_Tactics_Types.context t  in
           bind uu____1438
             (fun uu____1458  ->
                match uu____1458 with
                | (t1,typ,guard) ->
                    let uu____1470 =
                      must_trivial goal.FStar_Tactics_Types.context guard  in
                    bind uu____1470 (fun uu____1474  -> ret typ)))
       in
    FStar_All.pipe_left (wrap_err "tc") uu____1432
  
let (add_irrelevant_goal :
  Prims.string ->
    env ->
      FStar_Syntax_Syntax.typ -> FStar_Options.optionstate -> Prims.unit tac)
  =
  fun reason  ->
    fun env  ->
      fun phi  ->
        fun opts  ->
          let uu____1495 = mk_irrelevant_goal reason env phi opts  in
          bind uu____1495 (fun goal  -> add_goals [goal])
  
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
       let uu____1517 =
         istrivial goal.FStar_Tactics_Types.context
           goal.FStar_Tactics_Types.goal_ty
          in
       if uu____1517
       then solve goal FStar_Syntax_Util.exp_unit
       else
         (let uu____1521 =
            tts goal.FStar_Tactics_Types.context
              goal.FStar_Tactics_Types.goal_ty
             in
          fail1 "Not a trivial goal: %s" uu____1521))
  
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
          let uu____1538 =
            let uu____1539 = FStar_TypeChecker_Rel.simplify_guard e g  in
            uu____1539.FStar_TypeChecker_Env.guard_f  in
          match uu____1538 with
          | FStar_TypeChecker_Common.Trivial  -> ret ()
          | FStar_TypeChecker_Common.NonTrivial f ->
              let uu____1543 = istrivial e f  in
              if uu____1543
              then ret ()
              else
                (let uu____1547 = mk_irrelevant_goal reason e f opts  in
                 bind uu____1547
                   (fun goal  ->
                      let goal1 =
                        let uu___72_1554 = goal  in
                        {
                          FStar_Tactics_Types.context =
                            (uu___72_1554.FStar_Tactics_Types.context);
                          FStar_Tactics_Types.witness =
                            (uu___72_1554.FStar_Tactics_Types.witness);
                          FStar_Tactics_Types.goal_ty =
                            (uu___72_1554.FStar_Tactics_Types.goal_ty);
                          FStar_Tactics_Types.opts =
                            (uu___72_1554.FStar_Tactics_Types.opts);
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
          let uu____1575 =
            let uu____1576 = FStar_TypeChecker_Rel.simplify_guard e g  in
            uu____1576.FStar_TypeChecker_Env.guard_f  in
          match uu____1575 with
          | FStar_TypeChecker_Common.Trivial  ->
              ret FStar_Pervasives_Native.None
          | FStar_TypeChecker_Common.NonTrivial f ->
              let uu____1584 = istrivial e f  in
              if uu____1584
              then ret FStar_Pervasives_Native.None
              else
                (let uu____1592 = mk_irrelevant_goal reason e f opts  in
                 bind uu____1592
                   (fun goal  ->
                      ret
                        (FStar_Pervasives_Native.Some
                           (let uu___73_1602 = goal  in
                            {
                              FStar_Tactics_Types.context =
                                (uu___73_1602.FStar_Tactics_Types.context);
                              FStar_Tactics_Types.witness =
                                (uu___73_1602.FStar_Tactics_Types.witness);
                              FStar_Tactics_Types.goal_ty =
                                (uu___73_1602.FStar_Tactics_Types.goal_ty);
                              FStar_Tactics_Types.opts =
                                (uu___73_1602.FStar_Tactics_Types.opts);
                              FStar_Tactics_Types.is_guard = true
                            }))))
  
let (smt : Prims.unit tac) =
  bind cur_goal
    (fun g  ->
       let uu____1610 = is_irrelevant g  in
       if uu____1610
       then bind dismiss (fun uu____1614  -> add_smt_goals [g])
       else
         (let uu____1616 =
            tts g.FStar_Tactics_Types.context g.FStar_Tactics_Types.goal_ty
             in
          fail1 "goal is not irrelevant: cannot dispatch to smt (%s)"
            uu____1616))
  
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
             let uu____1657 =
               try
                 let uu____1691 =
                   let uu____1700 = FStar_BigInt.to_int_fs n1  in
                   FStar_List.splitAt uu____1700 p.FStar_Tactics_Types.goals
                    in
                 ret uu____1691
               with | uu____1722 -> fail "divide: not enough goals"  in
             bind uu____1657
               (fun uu____1749  ->
                  match uu____1749 with
                  | (lgs,rgs) ->
                      let lp =
                        let uu___74_1775 = p  in
                        {
                          FStar_Tactics_Types.main_context =
                            (uu___74_1775.FStar_Tactics_Types.main_context);
                          FStar_Tactics_Types.main_goal =
                            (uu___74_1775.FStar_Tactics_Types.main_goal);
                          FStar_Tactics_Types.all_implicits =
                            (uu___74_1775.FStar_Tactics_Types.all_implicits);
                          FStar_Tactics_Types.goals = lgs;
                          FStar_Tactics_Types.smt_goals = [];
                          FStar_Tactics_Types.depth =
                            (uu___74_1775.FStar_Tactics_Types.depth);
                          FStar_Tactics_Types.__dump =
                            (uu___74_1775.FStar_Tactics_Types.__dump);
                          FStar_Tactics_Types.psc =
                            (uu___74_1775.FStar_Tactics_Types.psc);
                          FStar_Tactics_Types.entry_range =
                            (uu___74_1775.FStar_Tactics_Types.entry_range)
                        }  in
                      let rp =
                        let uu___75_1777 = p  in
                        {
                          FStar_Tactics_Types.main_context =
                            (uu___75_1777.FStar_Tactics_Types.main_context);
                          FStar_Tactics_Types.main_goal =
                            (uu___75_1777.FStar_Tactics_Types.main_goal);
                          FStar_Tactics_Types.all_implicits =
                            (uu___75_1777.FStar_Tactics_Types.all_implicits);
                          FStar_Tactics_Types.goals = rgs;
                          FStar_Tactics_Types.smt_goals = [];
                          FStar_Tactics_Types.depth =
                            (uu___75_1777.FStar_Tactics_Types.depth);
                          FStar_Tactics_Types.__dump =
                            (uu___75_1777.FStar_Tactics_Types.__dump);
                          FStar_Tactics_Types.psc =
                            (uu___75_1777.FStar_Tactics_Types.psc);
                          FStar_Tactics_Types.entry_range =
                            (uu___75_1777.FStar_Tactics_Types.entry_range)
                        }  in
                      let uu____1778 = set lp  in
                      bind uu____1778
                        (fun uu____1786  ->
                           bind l
                             (fun a  ->
                                bind get
                                  (fun lp'  ->
                                     let uu____1800 = set rp  in
                                     bind uu____1800
                                       (fun uu____1808  ->
                                          bind r
                                            (fun b  ->
                                               bind get
                                                 (fun rp'  ->
                                                    let p' =
                                                      let uu___76_1824 = p
                                                         in
                                                      {
                                                        FStar_Tactics_Types.main_context
                                                          =
                                                          (uu___76_1824.FStar_Tactics_Types.main_context);
                                                        FStar_Tactics_Types.main_goal
                                                          =
                                                          (uu___76_1824.FStar_Tactics_Types.main_goal);
                                                        FStar_Tactics_Types.all_implicits
                                                          =
                                                          (uu___76_1824.FStar_Tactics_Types.all_implicits);
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
                                                          (uu___76_1824.FStar_Tactics_Types.depth);
                                                        FStar_Tactics_Types.__dump
                                                          =
                                                          (uu___76_1824.FStar_Tactics_Types.__dump);
                                                        FStar_Tactics_Types.psc
                                                          =
                                                          (uu___76_1824.FStar_Tactics_Types.psc);
                                                        FStar_Tactics_Types.entry_range
                                                          =
                                                          (uu___76_1824.FStar_Tactics_Types.entry_range)
                                                      }  in
                                                    let uu____1825 = set p'
                                                       in
                                                    bind uu____1825
                                                      (fun uu____1833  ->
                                                         ret (a, b))))))))))
  
let focus : 'a . 'a tac -> 'a tac =
  fun f  ->
    let uu____1851 = divide FStar_BigInt.one f idtac  in
    bind uu____1851
      (fun uu____1864  -> match uu____1864 with | (a,()) -> ret a)
  
let rec map : 'a . 'a tac -> 'a Prims.list tac =
  fun tau  ->
    bind get
      (fun p  ->
         match p.FStar_Tactics_Types.goals with
         | [] -> ret []
         | uu____1898::uu____1899 ->
             let uu____1902 =
               let uu____1911 = map tau  in
               divide FStar_BigInt.one tau uu____1911  in
             bind uu____1902
               (fun uu____1929  ->
                  match uu____1929 with | (h,t) -> ret (h :: t)))
  
let (seq : Prims.unit tac -> Prims.unit tac -> Prims.unit tac) =
  fun t1  ->
    fun t2  ->
      let uu____1966 =
        bind t1
          (fun uu____1971  ->
             let uu____1972 = map t2  in
             bind uu____1972 (fun uu____1980  -> ret ()))
         in
      focus uu____1966
  
let (intro : FStar_Syntax_Syntax.binder tac) =
  bind cur_goal
    (fun goal  ->
       let uu____1993 =
         FStar_Syntax_Util.arrow_one goal.FStar_Tactics_Types.goal_ty  in
       match uu____1993 with
       | FStar_Pervasives_Native.Some (b,c) ->
           let uu____2008 =
             let uu____2009 = FStar_Syntax_Util.is_total_comp c  in
             Prims.op_Negation uu____2009  in
           if uu____2008
           then fail "Codomain is effectful"
           else
             (let env' =
                FStar_TypeChecker_Env.push_binders
                  goal.FStar_Tactics_Types.context [b]
                 in
              let typ' = comp_to_typ c  in
              let uu____2015 = new_uvar "intro" env' typ'  in
              bind uu____2015
                (fun u  ->
                   let uu____2022 =
                     let uu____2023 =
                       FStar_Syntax_Util.abs [b] u
                         FStar_Pervasives_Native.None
                        in
                     trysolve goal uu____2023  in
                   if uu____2022
                   then
                     let uu____2026 =
                       let uu____2029 =
                         let uu___79_2030 = goal  in
                         let uu____2031 = bnorm env' u  in
                         let uu____2032 = bnorm env' typ'  in
                         {
                           FStar_Tactics_Types.context = env';
                           FStar_Tactics_Types.witness = uu____2031;
                           FStar_Tactics_Types.goal_ty = uu____2032;
                           FStar_Tactics_Types.opts =
                             (uu___79_2030.FStar_Tactics_Types.opts);
                           FStar_Tactics_Types.is_guard =
                             (uu___79_2030.FStar_Tactics_Types.is_guard)
                         }  in
                       replace_cur uu____2029  in
                     bind uu____2026 (fun uu____2034  -> ret b)
                   else fail "intro: unification failed"))
       | FStar_Pervasives_Native.None  ->
           let uu____2040 =
             tts goal.FStar_Tactics_Types.context
               goal.FStar_Tactics_Types.goal_ty
              in
           fail1 "intro: goal is not an arrow (%s)" uu____2040)
  
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
       (let uu____2067 =
          FStar_Syntax_Util.arrow_one goal.FStar_Tactics_Types.goal_ty  in
        match uu____2067 with
        | FStar_Pervasives_Native.Some (b,c) ->
            let uu____2086 =
              let uu____2087 = FStar_Syntax_Util.is_total_comp c  in
              Prims.op_Negation uu____2087  in
            if uu____2086
            then fail "Codomain is effectful"
            else
              (let bv =
                 FStar_Syntax_Syntax.gen_bv "__recf"
                   FStar_Pervasives_Native.None
                   goal.FStar_Tactics_Types.goal_ty
                  in
               let bs =
                 let uu____2103 = FStar_Syntax_Syntax.mk_binder bv  in
                 [uu____2103; b]  in
               let env' =
                 FStar_TypeChecker_Env.push_binders
                   goal.FStar_Tactics_Types.context bs
                  in
               let uu____2105 =
                 let uu____2108 = comp_to_typ c  in
                 new_uvar "intro_rec" env' uu____2108  in
               bind uu____2105
                 (fun u  ->
                    let lb =
                      let uu____2124 =
                        FStar_Syntax_Util.abs [b] u
                          FStar_Pervasives_Native.None
                         in
                      FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl bv) []
                        goal.FStar_Tactics_Types.goal_ty
                        FStar_Parser_Const.effect_Tot_lid uu____2124 []
                       in
                    let body = FStar_Syntax_Syntax.bv_to_name bv  in
                    let uu____2130 =
                      FStar_Syntax_Subst.close_let_rec [lb] body  in
                    match uu____2130 with
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
                          let uu____2167 =
                            let uu____2170 =
                              let uu___80_2171 = goal  in
                              let uu____2172 = bnorm env' u  in
                              let uu____2173 =
                                let uu____2174 = comp_to_typ c  in
                                bnorm env' uu____2174  in
                              {
                                FStar_Tactics_Types.context = env';
                                FStar_Tactics_Types.witness = uu____2172;
                                FStar_Tactics_Types.goal_ty = uu____2173;
                                FStar_Tactics_Types.opts =
                                  (uu___80_2171.FStar_Tactics_Types.opts);
                                FStar_Tactics_Types.is_guard =
                                  (uu___80_2171.FStar_Tactics_Types.is_guard)
                              }  in
                            replace_cur uu____2170  in
                          bind uu____2167
                            (fun uu____2181  ->
                               let uu____2182 =
                                 let uu____2187 =
                                   FStar_Syntax_Syntax.mk_binder bv  in
                                 (uu____2187, b)  in
                               ret uu____2182)
                        else fail "intro_rec: unification failed"))
        | FStar_Pervasives_Native.None  ->
            let uu____2201 =
              tts goal.FStar_Tactics_Types.context
                goal.FStar_Tactics_Types.goal_ty
               in
            fail1 "intro_rec: goal is not an arrow (%s)" uu____2201))
  
let (norm : FStar_Syntax_Embeddings.norm_step Prims.list -> Prims.unit tac) =
  fun s  ->
    bind cur_goal
      (fun goal  ->
         mlog
           (fun uu____2221  ->
              let uu____2222 =
                FStar_Syntax_Print.term_to_string
                  goal.FStar_Tactics_Types.witness
                 in
              FStar_Util.print1 "norm: witness = %s\n" uu____2222)
           (fun uu____2227  ->
              let steps =
                let uu____2231 = FStar_TypeChecker_Normalize.tr_norm_steps s
                   in
                FStar_List.append
                  [FStar_TypeChecker_Normalize.Reify;
                  FStar_TypeChecker_Normalize.UnfoldTac] uu____2231
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
                (let uu___81_2238 = goal  in
                 {
                   FStar_Tactics_Types.context =
                     (uu___81_2238.FStar_Tactics_Types.context);
                   FStar_Tactics_Types.witness = w;
                   FStar_Tactics_Types.goal_ty = t;
                   FStar_Tactics_Types.opts =
                     (uu___81_2238.FStar_Tactics_Types.opts);
                   FStar_Tactics_Types.is_guard =
                     (uu___81_2238.FStar_Tactics_Types.is_guard)
                 })))
  
let (norm_term_env :
  env ->
    FStar_Syntax_Embeddings.norm_step Prims.list ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac)
  =
  fun e  ->
    fun s  ->
      fun t  ->
        let uu____2256 =
          mlog
            (fun uu____2261  ->
               let uu____2262 = FStar_Syntax_Print.term_to_string t  in
               FStar_Util.print1 "norm_term: tm = %s\n" uu____2262)
            (fun uu____2264  ->
               bind get
                 (fun ps  ->
                    let uu____2268 = __tc e t  in
                    bind uu____2268
                      (fun uu____2290  ->
                         match uu____2290 with
                         | (t1,uu____2300,guard) ->
                             (FStar_TypeChecker_Rel.force_trivial_guard e
                                guard;
                              (let steps =
                                 let uu____2306 =
                                   FStar_TypeChecker_Normalize.tr_norm_steps
                                     s
                                    in
                                 FStar_List.append
                                   [FStar_TypeChecker_Normalize.Reify;
                                   FStar_TypeChecker_Normalize.UnfoldTac]
                                   uu____2306
                                  in
                               let t2 =
                                 normalize steps
                                   ps.FStar_Tactics_Types.main_context t1
                                  in
                               ret t2)))))
           in
        FStar_All.pipe_left (wrap_err "norm_term") uu____2256
  
let (refine_intro : Prims.unit tac) =
  let uu____2318 =
    bind cur_goal
      (fun g  ->
         let uu____2325 =
           FStar_TypeChecker_Rel.base_and_refinement
             g.FStar_Tactics_Types.context g.FStar_Tactics_Types.goal_ty
            in
         match uu____2325 with
         | (uu____2338,FStar_Pervasives_Native.None ) ->
             fail "not a refinement"
         | (t,FStar_Pervasives_Native.Some (bv,phi)) ->
             let g1 =
               let uu___82_2363 = g  in
               {
                 FStar_Tactics_Types.context =
                   (uu___82_2363.FStar_Tactics_Types.context);
                 FStar_Tactics_Types.witness =
                   (uu___82_2363.FStar_Tactics_Types.witness);
                 FStar_Tactics_Types.goal_ty = t;
                 FStar_Tactics_Types.opts =
                   (uu___82_2363.FStar_Tactics_Types.opts);
                 FStar_Tactics_Types.is_guard =
                   (uu___82_2363.FStar_Tactics_Types.is_guard)
               }  in
             let uu____2364 =
               let uu____2369 =
                 let uu____2374 =
                   let uu____2375 = FStar_Syntax_Syntax.mk_binder bv  in
                   [uu____2375]  in
                 FStar_Syntax_Subst.open_term uu____2374 phi  in
               match uu____2369 with
               | (bvs,phi1) ->
                   let uu____2382 =
                     let uu____2383 = FStar_List.hd bvs  in
                     FStar_Pervasives_Native.fst uu____2383  in
                   (uu____2382, phi1)
                in
             (match uu____2364 with
              | (bv1,phi1) ->
                  let uu____2396 =
                    let uu____2399 =
                      FStar_Syntax_Subst.subst
                        [FStar_Syntax_Syntax.NT
                           (bv1, (g.FStar_Tactics_Types.witness))] phi1
                       in
                    mk_irrelevant_goal "refine_intro refinement"
                      g.FStar_Tactics_Types.context uu____2399
                      g.FStar_Tactics_Types.opts
                     in
                  bind uu____2396
                    (fun g2  ->
                       bind dismiss (fun uu____2403  -> add_goals [g1; g2]))))
     in
  FStar_All.pipe_left (wrap_err "refine_intro") uu____2318 
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
             let uu____2427 = __tc env t  in
             bind uu____2427
               (fun uu____2447  ->
                  match uu____2447 with
                  | (t1,typ,guard) ->
                      let uu____2459 =
                        if force_guard
                        then
                          must_trivial goal.FStar_Tactics_Types.context guard
                        else
                          add_goal_from_guard "__exact typing"
                            goal.FStar_Tactics_Types.context guard
                            goal.FStar_Tactics_Types.opts
                         in
                      bind uu____2459
                        (fun uu____2466  ->
                           mlog
                             (fun uu____2470  ->
                                let uu____2471 =
                                  tts goal.FStar_Tactics_Types.context typ
                                   in
                                let uu____2472 =
                                  tts goal.FStar_Tactics_Types.context
                                    goal.FStar_Tactics_Types.goal_ty
                                   in
                                FStar_Util.print2
                                  "exact: unifying %s and %s\n" uu____2471
                                  uu____2472)
                             (fun uu____2475  ->
                                let uu____2476 =
                                  do_unify goal.FStar_Tactics_Types.context
                                    typ goal.FStar_Tactics_Types.goal_ty
                                   in
                                if uu____2476
                                then solve goal t1
                                else
                                  (let uu____2480 =
                                     tts goal.FStar_Tactics_Types.context t1
                                      in
                                   let uu____2481 =
                                     tts goal.FStar_Tactics_Types.context typ
                                      in
                                   let uu____2482 =
                                     tts goal.FStar_Tactics_Types.context
                                       goal.FStar_Tactics_Types.goal_ty
                                      in
                                   let uu____2483 =
                                     tts goal.FStar_Tactics_Types.context
                                       goal.FStar_Tactics_Types.witness
                                      in
                                   fail4
                                     "%s : %s does not exactly solve the goal %s (witness = %s)"
                                     uu____2480 uu____2481 uu____2482
                                     uu____2483)))))
  
let (t_exact :
  Prims.bool -> Prims.bool -> FStar_Syntax_Syntax.term -> Prims.unit tac) =
  fun set_expected_typ1  ->
    fun force_guard  ->
      fun tm  ->
        let uu____2497 =
          mlog
            (fun uu____2502  ->
               let uu____2503 = FStar_Syntax_Print.term_to_string tm  in
               FStar_Util.print1 "t_exact: tm = %s\n" uu____2503)
            (fun uu____2506  ->
               let uu____2507 =
                 let uu____2514 =
                   __exact_now set_expected_typ1 force_guard tm  in
                 trytac' uu____2514  in
               bind uu____2507
                 (fun uu___56_2523  ->
                    match uu___56_2523 with
                    | FStar_Util.Inr r -> ret ()
                    | FStar_Util.Inl e ->
                        let uu____2532 =
                          let uu____2539 =
                            let uu____2542 =
                              norm [FStar_Syntax_Embeddings.Delta]  in
                            bind uu____2542
                              (fun uu____2546  ->
                                 bind refine_intro
                                   (fun uu____2548  ->
                                      __exact_now set_expected_typ1
                                        force_guard tm))
                             in
                          trytac' uu____2539  in
                        bind uu____2532
                          (fun uu___55_2555  ->
                             match uu___55_2555 with
                             | FStar_Util.Inr r -> ret ()
                             | FStar_Util.Inl uu____2563 -> fail e)))
           in
        FStar_All.pipe_left (wrap_err "exact") uu____2497
  
let (uvar_free_in_goal :
  FStar_Syntax_Syntax.uvar -> FStar_Tactics_Types.goal -> Prims.bool) =
  fun u  ->
    fun g  ->
      if g.FStar_Tactics_Types.is_guard
      then false
      else
        (let free_uvars =
           let uu____2578 =
             let uu____2585 =
               FStar_Syntax_Free.uvars g.FStar_Tactics_Types.goal_ty  in
             FStar_Util.set_elements uu____2585  in
           FStar_List.map FStar_Pervasives_Native.fst uu____2578  in
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
          let uu____2645 = f x  in
          bind uu____2645
            (fun y  ->
               let uu____2653 = mapM f xs  in
               bind uu____2653 (fun ys  -> ret (y :: ys)))
  
exception NoUnif 
let (uu___is_NoUnif : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with | NoUnif  -> true | uu____2671 -> false
  
let rec (__apply :
  Prims.bool ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.typ -> Prims.unit tac)
  =
  fun uopt  ->
    fun tm  ->
      fun typ  ->
        bind cur_goal
          (fun goal  ->
             let uu____2688 =
               let uu____2693 = t_exact false true tm  in trytac uu____2693
                in
             bind uu____2688
               (fun uu___57_2700  ->
                  match uu___57_2700 with
                  | FStar_Pervasives_Native.Some r -> ret ()
                  | FStar_Pervasives_Native.None  ->
                      let uu____2706 = FStar_Syntax_Util.arrow_one typ  in
                      (match uu____2706 with
                       | FStar_Pervasives_Native.None  ->
                           FStar_Exn.raise NoUnif
                       | FStar_Pervasives_Native.Some ((bv,aq),c) ->
                           mlog
                             (fun uu____2738  ->
                                let uu____2739 =
                                  FStar_Syntax_Print.binder_to_string
                                    (bv, aq)
                                   in
                                FStar_Util.print1
                                  "__apply: pushing binder %s\n" uu____2739)
                             (fun uu____2742  ->
                                let uu____2743 =
                                  let uu____2744 =
                                    FStar_Syntax_Util.is_total_comp c  in
                                  Prims.op_Negation uu____2744  in
                                if uu____2743
                                then fail "apply: not total codomain"
                                else
                                  (let uu____2748 =
                                     new_uvar "apply"
                                       goal.FStar_Tactics_Types.context
                                       bv.FStar_Syntax_Syntax.sort
                                      in
                                   bind uu____2748
                                     (fun u  ->
                                        let tm' =
                                          FStar_Syntax_Syntax.mk_Tm_app tm
                                            [(u, aq)]
                                            FStar_Pervasives_Native.None
                                            (goal.FStar_Tactics_Types.context).FStar_TypeChecker_Env.range
                                           in
                                        let typ' =
                                          let uu____2768 = comp_to_typ c  in
                                          FStar_All.pipe_left
                                            (FStar_Syntax_Subst.subst
                                               [FStar_Syntax_Syntax.NT
                                                  (bv, u)]) uu____2768
                                           in
                                        let uu____2769 =
                                          __apply uopt tm' typ'  in
                                        bind uu____2769
                                          (fun uu____2777  ->
                                             let u1 =
                                               bnorm
                                                 goal.FStar_Tactics_Types.context
                                                 u
                                                in
                                             let uu____2779 =
                                               let uu____2780 =
                                                 let uu____2783 =
                                                   let uu____2784 =
                                                     FStar_Syntax_Util.head_and_args
                                                       u1
                                                      in
                                                   FStar_Pervasives_Native.fst
                                                     uu____2784
                                                    in
                                                 FStar_Syntax_Subst.compress
                                                   uu____2783
                                                  in
                                               uu____2780.FStar_Syntax_Syntax.n
                                                in
                                             match uu____2779 with
                                             | FStar_Syntax_Syntax.Tm_uvar
                                                 (uvar,uu____2812) ->
                                                 bind get
                                                   (fun ps  ->
                                                      let uu____2840 =
                                                        uopt &&
                                                          (uvar_free uvar ps)
                                                         in
                                                      if uu____2840
                                                      then ret ()
                                                      else
                                                        (let uu____2844 =
                                                           let uu____2847 =
                                                             let uu___83_2848
                                                               = goal  in
                                                             let uu____2849 =
                                                               bnorm
                                                                 goal.FStar_Tactics_Types.context
                                                                 u1
                                                                in
                                                             let uu____2850 =
                                                               bnorm
                                                                 goal.FStar_Tactics_Types.context
                                                                 bv.FStar_Syntax_Syntax.sort
                                                                in
                                                             {
                                                               FStar_Tactics_Types.context
                                                                 =
                                                                 (uu___83_2848.FStar_Tactics_Types.context);
                                                               FStar_Tactics_Types.witness
                                                                 = uu____2849;
                                                               FStar_Tactics_Types.goal_ty
                                                                 = uu____2850;
                                                               FStar_Tactics_Types.opts
                                                                 =
                                                                 (uu___83_2848.FStar_Tactics_Types.opts);
                                                               FStar_Tactics_Types.is_guard
                                                                 = false
                                                             }  in
                                                           [uu____2847]  in
                                                         add_goals uu____2844))
                                             | t -> ret ())))))))
  
let try_unif : 'a . 'a tac -> 'a tac -> 'a tac =
  fun t  ->
    fun t'  -> mk_tac (fun ps  -> try run t ps with | NoUnif  -> run t' ps)
  
let (apply : Prims.bool -> FStar_Syntax_Syntax.term -> Prims.unit tac) =
  fun uopt  ->
    fun tm  ->
      let uu____2896 =
        mlog
          (fun uu____2901  ->
             let uu____2902 = FStar_Syntax_Print.term_to_string tm  in
             FStar_Util.print1 "apply: tm = %s\n" uu____2902)
          (fun uu____2904  ->
             bind cur_goal
               (fun goal  ->
                  let uu____2908 = __tc goal.FStar_Tactics_Types.context tm
                     in
                  bind uu____2908
                    (fun uu____2929  ->
                       match uu____2929 with
                       | (tm1,typ,guard) ->
                           let uu____2941 =
                             let uu____2944 =
                               let uu____2947 = __apply uopt tm1 typ  in
                               bind uu____2947
                                 (fun uu____2951  ->
                                    add_goal_from_guard "apply guard"
                                      goal.FStar_Tactics_Types.context guard
                                      goal.FStar_Tactics_Types.opts)
                                in
                             focus uu____2944  in
                           let uu____2952 =
                             let uu____2955 =
                               tts goal.FStar_Tactics_Types.context tm1  in
                             let uu____2956 =
                               tts goal.FStar_Tactics_Types.context typ  in
                             let uu____2957 =
                               tts goal.FStar_Tactics_Types.context
                                 goal.FStar_Tactics_Types.goal_ty
                                in
                             fail3
                               "Cannot instantiate %s (of type %s) to match goal (%s)"
                               uu____2955 uu____2956 uu____2957
                              in
                           try_unif uu____2941 uu____2952)))
         in
      FStar_All.pipe_left (wrap_err "apply") uu____2896
  
let (apply_lemma : FStar_Syntax_Syntax.term -> Prims.unit tac) =
  fun tm  ->
    let uu____2969 =
      let uu____2972 =
        mlog
          (fun uu____2977  ->
             let uu____2978 = FStar_Syntax_Print.term_to_string tm  in
             FStar_Util.print1 "apply_lemma: tm = %s\n" uu____2978)
          (fun uu____2981  ->
             let is_unit_t t =
               let uu____2986 =
                 let uu____2987 = FStar_Syntax_Subst.compress t  in
                 uu____2987.FStar_Syntax_Syntax.n  in
               match uu____2986 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.unit_lid
                   -> true
               | uu____2991 -> false  in
             bind cur_goal
               (fun goal  ->
                  let uu____2995 = __tc goal.FStar_Tactics_Types.context tm
                     in
                  bind uu____2995
                    (fun uu____3017  ->
                       match uu____3017 with
                       | (tm1,t,guard) ->
                           let uu____3029 =
                             FStar_Syntax_Util.arrow_formals_comp t  in
                           (match uu____3029 with
                            | (bs,comp) ->
                                if
                                  Prims.op_Negation
                                    (FStar_Syntax_Util.is_lemma_comp comp)
                                then fail "not a lemma"
                                else
                                  (let uu____3059 =
                                     FStar_List.fold_left
                                       (fun uu____3105  ->
                                          fun uu____3106  ->
                                            match (uu____3105, uu____3106)
                                            with
                                            | ((uvs,guard1,subst1),(b,aq)) ->
                                                let b_t =
                                                  FStar_Syntax_Subst.subst
                                                    subst1
                                                    b.FStar_Syntax_Syntax.sort
                                                   in
                                                let uu____3209 =
                                                  is_unit_t b_t  in
                                                if uu____3209
                                                then
                                                  (((FStar_Syntax_Util.exp_unit,
                                                      aq) :: uvs), guard1,
                                                    ((FStar_Syntax_Syntax.NT
                                                        (b,
                                                          FStar_Syntax_Util.exp_unit))
                                                    :: subst1))
                                                else
                                                  (let uu____3247 =
                                                     FStar_TypeChecker_Util.new_implicit_var
                                                       "apply_lemma"
                                                       (goal.FStar_Tactics_Types.goal_ty).FStar_Syntax_Syntax.pos
                                                       goal.FStar_Tactics_Types.context
                                                       b_t
                                                      in
                                                   match uu____3247 with
                                                   | (u,uu____3277,g_u) ->
                                                       let uu____3291 =
                                                         FStar_TypeChecker_Rel.conj_guard
                                                           guard1 g_u
                                                          in
                                                       (((u, aq) :: uvs),
                                                         uu____3291,
                                                         ((FStar_Syntax_Syntax.NT
                                                             (b, u)) ::
                                                         subst1))))
                                       ([], guard, []) bs
                                      in
                                   match uu____3059 with
                                   | (uvs,implicits,subst1) ->
                                       let uvs1 = FStar_List.rev uvs  in
                                       let comp1 =
                                         FStar_Syntax_Subst.subst_comp subst1
                                           comp
                                          in
                                       let uu____3361 =
                                         let uu____3370 =
                                           let uu____3379 =
                                             FStar_Syntax_Util.comp_to_comp_typ
                                               comp1
                                              in
                                           uu____3379.FStar_Syntax_Syntax.effect_args
                                            in
                                         match uu____3370 with
                                         | pre::post::uu____3390 ->
                                             ((FStar_Pervasives_Native.fst
                                                 pre),
                                               (FStar_Pervasives_Native.fst
                                                  post))
                                         | uu____3431 ->
                                             failwith
                                               "apply_lemma: impossible: not a lemma"
                                          in
                                       (match uu____3361 with
                                        | (pre,post) ->
                                            let post1 =
                                              let uu____3463 =
                                                let uu____3472 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    FStar_Syntax_Util.exp_unit
                                                   in
                                                [uu____3472]  in
                                              FStar_Syntax_Util.mk_app post
                                                uu____3463
                                               in
                                            let uu____3473 =
                                              let uu____3474 =
                                                let uu____3475 =
                                                  FStar_Syntax_Util.mk_squash
                                                    FStar_Syntax_Syntax.U_zero
                                                    post1
                                                   in
                                                do_unify
                                                  goal.FStar_Tactics_Types.context
                                                  uu____3475
                                                  goal.FStar_Tactics_Types.goal_ty
                                                 in
                                              Prims.op_Negation uu____3474
                                               in
                                            if uu____3473
                                            then
                                              let uu____3478 =
                                                tts
                                                  goal.FStar_Tactics_Types.context
                                                  tm1
                                                 in
                                              let uu____3479 =
                                                let uu____3480 =
                                                  FStar_Syntax_Util.mk_squash
                                                    FStar_Syntax_Syntax.U_zero
                                                    post1
                                                   in
                                                tts
                                                  goal.FStar_Tactics_Types.context
                                                  uu____3480
                                                 in
                                              let uu____3481 =
                                                tts
                                                  goal.FStar_Tactics_Types.context
                                                  goal.FStar_Tactics_Types.goal_ty
                                                 in
                                              fail3
                                                "Cannot instantiate lemma %s (with postcondition: %s) to match goal (%s)"
                                                uu____3478 uu____3479
                                                uu____3481
                                            else
                                              (let uu____3483 =
                                                 add_implicits
                                                   implicits.FStar_TypeChecker_Env.implicits
                                                  in
                                               bind uu____3483
                                                 (fun uu____3488  ->
                                                    let uu____3489 =
                                                      solve goal
                                                        FStar_Syntax_Util.exp_unit
                                                       in
                                                    bind uu____3489
                                                      (fun uu____3497  ->
                                                         let is_free_uvar uv
                                                           t1 =
                                                           let free_uvars =
                                                             let uu____3508 =
                                                               let uu____3515
                                                                 =
                                                                 FStar_Syntax_Free.uvars
                                                                   t1
                                                                  in
                                                               FStar_Util.set_elements
                                                                 uu____3515
                                                                in
                                                             FStar_List.map
                                                               FStar_Pervasives_Native.fst
                                                               uu____3508
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
                                                           let uu____3556 =
                                                             FStar_Syntax_Util.head_and_args
                                                               t1
                                                              in
                                                           match uu____3556
                                                           with
                                                           | (hd1,uu____3572)
                                                               ->
                                                               (match 
                                                                  hd1.FStar_Syntax_Syntax.n
                                                                with
                                                                | FStar_Syntax_Syntax.Tm_uvar
                                                                    (uv,uu____3594)
                                                                    ->
                                                                    appears
                                                                    uv goals
                                                                | uu____3619
                                                                    -> false)
                                                            in
                                                         let uu____3620 =
                                                           FStar_All.pipe_right
                                                             implicits.FStar_TypeChecker_Env.implicits
                                                             (mapM
                                                                (fun
                                                                   uu____3692
                                                                    ->
                                                                   match uu____3692
                                                                   with
                                                                   | 
                                                                   (_msg,env,_uvar,term,typ,uu____3720)
                                                                    ->
                                                                    let uu____3721
                                                                    =
                                                                    FStar_Syntax_Util.head_and_args
                                                                    term  in
                                                                    (match uu____3721
                                                                    with
                                                                    | 
                                                                    (hd1,uu____3747)
                                                                    ->
                                                                    let uu____3768
                                                                    =
                                                                    let uu____3769
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    hd1  in
                                                                    uu____3769.FStar_Syntax_Syntax.n
                                                                     in
                                                                    (match uu____3768
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Tm_uvar
                                                                    uu____3782
                                                                    ->
                                                                    let uu____3799
                                                                    =
                                                                    let uu____3808
                                                                    =
                                                                    let uu____3811
                                                                    =
                                                                    let uu___86_3812
                                                                    = goal
                                                                     in
                                                                    let uu____3813
                                                                    =
                                                                    bnorm
                                                                    goal.FStar_Tactics_Types.context
                                                                    term  in
                                                                    let uu____3814
                                                                    =
                                                                    bnorm
                                                                    goal.FStar_Tactics_Types.context
                                                                    typ  in
                                                                    {
                                                                    FStar_Tactics_Types.context
                                                                    =
                                                                    (uu___86_3812.FStar_Tactics_Types.context);
                                                                    FStar_Tactics_Types.witness
                                                                    =
                                                                    uu____3813;
                                                                    FStar_Tactics_Types.goal_ty
                                                                    =
                                                                    uu____3814;
                                                                    FStar_Tactics_Types.opts
                                                                    =
                                                                    (uu___86_3812.FStar_Tactics_Types.opts);
                                                                    FStar_Tactics_Types.is_guard
                                                                    =
                                                                    (uu___86_3812.FStar_Tactics_Types.is_guard)
                                                                    }  in
                                                                    [uu____3811]
                                                                     in
                                                                    (uu____3808,
                                                                    [])  in
                                                                    ret
                                                                    uu____3799
                                                                    | 
                                                                    uu____3827
                                                                    ->
                                                                    let g_typ
                                                                    =
                                                                    let uu____3829
                                                                    =
                                                                    FStar_Options.__temp_fast_implicits
                                                                    ()  in
                                                                    if
                                                                    uu____3829
                                                                    then
                                                                    FStar_TypeChecker_TcTerm.check_type_of_well_typed_term
                                                                    false env
                                                                    term typ
                                                                    else
                                                                    (let term1
                                                                    =
                                                                    bnorm env
                                                                    term  in
                                                                    let uu____3832
                                                                    =
                                                                    let uu____3839
                                                                    =
                                                                    FStar_TypeChecker_Env.set_expected_typ
                                                                    env typ
                                                                     in
                                                                    env.FStar_TypeChecker_Env.type_of
                                                                    uu____3839
                                                                    term1  in
                                                                    match uu____3832
                                                                    with
                                                                    | 
                                                                    (uu____3840,uu____3841,g_typ)
                                                                    -> g_typ)
                                                                     in
                                                                    let uu____3843
                                                                    =
                                                                    goal_from_guard
                                                                    "apply_lemma solved arg"
                                                                    goal.FStar_Tactics_Types.context
                                                                    g_typ
                                                                    goal.FStar_Tactics_Types.opts
                                                                     in
                                                                    bind
                                                                    uu____3843
                                                                    (fun
                                                                    uu___58_3859
                                                                     ->
                                                                    match uu___58_3859
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
                                                         bind uu____3620
                                                           (fun goals_  ->
                                                              let sub_goals =
                                                                let uu____3927
                                                                  =
                                                                  FStar_List.map
                                                                    FStar_Pervasives_Native.fst
                                                                    goals_
                                                                   in
                                                                FStar_List.flatten
                                                                  uu____3927
                                                                 in
                                                              let smt_goals =
                                                                let uu____3949
                                                                  =
                                                                  FStar_List.map
                                                                    FStar_Pervasives_Native.snd
                                                                    goals_
                                                                   in
                                                                FStar_List.flatten
                                                                  uu____3949
                                                                 in
                                                              let rec filter'
                                                                a f xs =
                                                                match xs with
                                                                | [] -> []
                                                                | x::xs1 ->
                                                                    let uu____4004
                                                                    = f x xs1
                                                                     in
                                                                    if
                                                                    uu____4004
                                                                    then
                                                                    let uu____4007
                                                                    =
                                                                    filter'
                                                                    () f xs1
                                                                     in x ::
                                                                    uu____4007
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
                                                                    let uu____4021
                                                                    =
                                                                    checkone
                                                                    g.FStar_Tactics_Types.witness
                                                                    goals  in
                                                                    Prims.op_Negation
                                                                    uu____4021))
                                                                    a434 a435)
                                                                    (Obj.magic
                                                                    sub_goals))
                                                                 in
                                                              let uu____4022
                                                                =
                                                                add_goal_from_guard
                                                                  "apply_lemma guard"
                                                                  goal.FStar_Tactics_Types.context
                                                                  guard
                                                                  goal.FStar_Tactics_Types.opts
                                                                 in
                                                              bind uu____4022
                                                                (fun
                                                                   uu____4027
                                                                    ->
                                                                   let uu____4028
                                                                    =
                                                                    let uu____4031
                                                                    =
                                                                    let uu____4032
                                                                    =
                                                                    let uu____4033
                                                                    =
                                                                    FStar_Syntax_Util.mk_squash
                                                                    FStar_Syntax_Syntax.U_zero
                                                                    pre  in
                                                                    istrivial
                                                                    goal.FStar_Tactics_Types.context
                                                                    uu____4033
                                                                     in
                                                                    Prims.op_Negation
                                                                    uu____4032
                                                                     in
                                                                    if
                                                                    uu____4031
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
                                                                    uu____4028
                                                                    (fun
                                                                    uu____4039
                                                                     ->
                                                                    let uu____4040
                                                                    =
                                                                    add_smt_goals
                                                                    smt_goals
                                                                     in
                                                                    bind
                                                                    uu____4040
                                                                    (fun
                                                                    uu____4044
                                                                     ->
                                                                    add_goals
                                                                    sub_goals1)))))))))))))
         in
      focus uu____2972  in
    FStar_All.pipe_left (wrap_err "apply_lemma") uu____2969
  
let (destruct_eq' :
  FStar_Syntax_Syntax.typ ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun typ  ->
    let uu____4064 = FStar_Syntax_Util.destruct_typ_as_formula typ  in
    match uu____4064 with
    | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn
        (l,uu____4074::(e1,uu____4076)::(e2,uu____4078)::[])) when
        FStar_Ident.lid_equals l FStar_Parser_Const.eq2_lid ->
        FStar_Pervasives_Native.Some (e1, e2)
    | uu____4137 -> FStar_Pervasives_Native.None
  
let (destruct_eq :
  FStar_Syntax_Syntax.typ ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun typ  ->
    let uu____4159 = destruct_eq' typ  in
    match uu____4159 with
    | FStar_Pervasives_Native.Some t -> FStar_Pervasives_Native.Some t
    | FStar_Pervasives_Native.None  ->
        let uu____4189 = FStar_Syntax_Util.un_squash typ  in
        (match uu____4189 with
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
        let uu____4245 = FStar_TypeChecker_Env.pop_bv e1  in
        match uu____4245 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (bv',e') ->
            if FStar_Syntax_Syntax.bv_eq bvar bv'
            then FStar_Pervasives_Native.Some (e', [])
            else
              (let uu____4293 = aux e'  in
               FStar_Util.map_opt uu____4293
                 (fun uu____4317  ->
                    match uu____4317 with | (e'',bvs) -> (e'', (bv' :: bvs))))
         in
      let uu____4338 = aux e  in
      FStar_Util.map_opt uu____4338
        (fun uu____4362  ->
           match uu____4362 with | (e',bvs) -> (e', (FStar_List.rev bvs)))
  
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
          let uu____4417 = split_env b1 g.FStar_Tactics_Types.context  in
          FStar_Util.map_opt uu____4417
            (fun uu____4441  ->
               match uu____4441 with
               | (e0,bvs) ->
                   let s1 bv =
                     let uu___87_4458 = bv  in
                     let uu____4459 =
                       FStar_Syntax_Subst.subst s bv.FStar_Syntax_Syntax.sort
                        in
                     {
                       FStar_Syntax_Syntax.ppname =
                         (uu___87_4458.FStar_Syntax_Syntax.ppname);
                       FStar_Syntax_Syntax.index =
                         (uu___87_4458.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort = uu____4459
                     }  in
                   let bvs1 = FStar_List.map s1 bvs  in
                   let c = push_bvs e0 (b2 :: bvs1)  in
                   let w =
                     FStar_Syntax_Subst.subst s g.FStar_Tactics_Types.witness
                      in
                   let t =
                     FStar_Syntax_Subst.subst s g.FStar_Tactics_Types.goal_ty
                      in
                   let uu___88_4468 = g  in
                   {
                     FStar_Tactics_Types.context = c;
                     FStar_Tactics_Types.witness = w;
                     FStar_Tactics_Types.goal_ty = t;
                     FStar_Tactics_Types.opts =
                       (uu___88_4468.FStar_Tactics_Types.opts);
                     FStar_Tactics_Types.is_guard =
                       (uu___88_4468.FStar_Tactics_Types.is_guard)
                   })
  
let (rewrite : FStar_Syntax_Syntax.binder -> Prims.unit tac) =
  fun h  ->
    bind cur_goal
      (fun goal  ->
         let uu____4481 = h  in
         match uu____4481 with
         | (bv,uu____4485) ->
             mlog
               (fun uu____4489  ->
                  let uu____4490 = FStar_Syntax_Print.bv_to_string bv  in
                  let uu____4491 =
                    tts goal.FStar_Tactics_Types.context
                      bv.FStar_Syntax_Syntax.sort
                     in
                  FStar_Util.print2 "+++Rewrite %s : %s\n" uu____4490
                    uu____4491)
               (fun uu____4494  ->
                  let uu____4495 =
                    split_env bv goal.FStar_Tactics_Types.context  in
                  match uu____4495 with
                  | FStar_Pervasives_Native.None  ->
                      fail "rewrite: binder not found in environment"
                  | FStar_Pervasives_Native.Some (e0,bvs) ->
                      let uu____4524 =
                        destruct_eq bv.FStar_Syntax_Syntax.sort  in
                      (match uu____4524 with
                       | FStar_Pervasives_Native.Some (x,e) ->
                           let uu____4539 =
                             let uu____4540 = FStar_Syntax_Subst.compress x
                                in
                             uu____4540.FStar_Syntax_Syntax.n  in
                           (match uu____4539 with
                            | FStar_Syntax_Syntax.Tm_name x1 ->
                                let s = [FStar_Syntax_Syntax.NT (x1, e)]  in
                                let s1 bv1 =
                                  let uu___89_4553 = bv1  in
                                  let uu____4554 =
                                    FStar_Syntax_Subst.subst s
                                      bv1.FStar_Syntax_Syntax.sort
                                     in
                                  {
                                    FStar_Syntax_Syntax.ppname =
                                      (uu___89_4553.FStar_Syntax_Syntax.ppname);
                                    FStar_Syntax_Syntax.index =
                                      (uu___89_4553.FStar_Syntax_Syntax.index);
                                    FStar_Syntax_Syntax.sort = uu____4554
                                  }  in
                                let bvs1 = FStar_List.map s1 bvs  in
                                let uu____4560 =
                                  let uu___90_4561 = goal  in
                                  let uu____4562 = push_bvs e0 (bv :: bvs1)
                                     in
                                  let uu____4563 =
                                    FStar_Syntax_Subst.subst s
                                      goal.FStar_Tactics_Types.witness
                                     in
                                  let uu____4564 =
                                    FStar_Syntax_Subst.subst s
                                      goal.FStar_Tactics_Types.goal_ty
                                     in
                                  {
                                    FStar_Tactics_Types.context = uu____4562;
                                    FStar_Tactics_Types.witness = uu____4563;
                                    FStar_Tactics_Types.goal_ty = uu____4564;
                                    FStar_Tactics_Types.opts =
                                      (uu___90_4561.FStar_Tactics_Types.opts);
                                    FStar_Tactics_Types.is_guard =
                                      (uu___90_4561.FStar_Tactics_Types.is_guard)
                                  }  in
                                replace_cur uu____4560
                            | uu____4565 ->
                                fail
                                  "rewrite: Not an equality hypothesis with a variable on the LHS")
                       | uu____4566 ->
                           fail "rewrite: Not an equality hypothesis")))
  
let (rename_to :
  FStar_Syntax_Syntax.binder -> Prims.string -> Prims.unit tac) =
  fun b  ->
    fun s  ->
      bind cur_goal
        (fun goal  ->
           let uu____4591 = b  in
           match uu____4591 with
           | (bv,uu____4595) ->
               let bv' =
                 FStar_Syntax_Syntax.freshen_bv
                   (let uu___91_4599 = bv  in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (FStar_Ident.mk_ident
                           (s,
                             ((bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange)));
                      FStar_Syntax_Syntax.index =
                        (uu___91_4599.FStar_Syntax_Syntax.index);
                      FStar_Syntax_Syntax.sort =
                        (uu___91_4599.FStar_Syntax_Syntax.sort)
                    })
                  in
               let s1 =
                 let uu____4603 =
                   let uu____4604 =
                     let uu____4611 = FStar_Syntax_Syntax.bv_to_name bv'  in
                     (bv, uu____4611)  in
                   FStar_Syntax_Syntax.NT uu____4604  in
                 [uu____4603]  in
               let uu____4612 = subst_goal bv bv' s1 goal  in
               (match uu____4612 with
                | FStar_Pervasives_Native.None  ->
                    fail "rename_to: binder not found in environment"
                | FStar_Pervasives_Native.Some goal1 -> replace_cur goal1))
  
let (binder_retype : FStar_Syntax_Syntax.binder -> Prims.unit tac) =
  fun b  ->
    bind cur_goal
      (fun goal  ->
         let uu____4631 = b  in
         match uu____4631 with
         | (bv,uu____4635) ->
             let uu____4636 = split_env bv goal.FStar_Tactics_Types.context
                in
             (match uu____4636 with
              | FStar_Pervasives_Native.None  ->
                  fail "binder_retype: binder is not present in environment"
              | FStar_Pervasives_Native.Some (e0,bvs) ->
                  let uu____4665 = FStar_Syntax_Util.type_u ()  in
                  (match uu____4665 with
                   | (ty,u) ->
                       let uu____4674 = new_uvar "binder_retype" e0 ty  in
                       bind uu____4674
                         (fun t'  ->
                            let bv'' =
                              let uu___92_4684 = bv  in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___92_4684.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___92_4684.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = t'
                              }  in
                            let s =
                              let uu____4688 =
                                let uu____4689 =
                                  let uu____4696 =
                                    FStar_Syntax_Syntax.bv_to_name bv''  in
                                  (bv, uu____4696)  in
                                FStar_Syntax_Syntax.NT uu____4689  in
                              [uu____4688]  in
                            let bvs1 =
                              FStar_List.map
                                (fun b1  ->
                                   let uu___93_4704 = b1  in
                                   let uu____4705 =
                                     FStar_Syntax_Subst.subst s
                                       b1.FStar_Syntax_Syntax.sort
                                      in
                                   {
                                     FStar_Syntax_Syntax.ppname =
                                       (uu___93_4704.FStar_Syntax_Syntax.ppname);
                                     FStar_Syntax_Syntax.index =
                                       (uu___93_4704.FStar_Syntax_Syntax.index);
                                     FStar_Syntax_Syntax.sort = uu____4705
                                   }) bvs
                               in
                            let env' = push_bvs e0 (bv'' :: bvs1)  in
                            bind dismiss
                              (fun uu____4711  ->
                                 let uu____4712 =
                                   let uu____4715 =
                                     let uu____4718 =
                                       let uu___94_4719 = goal  in
                                       let uu____4720 =
                                         FStar_Syntax_Subst.subst s
                                           goal.FStar_Tactics_Types.witness
                                          in
                                       let uu____4721 =
                                         FStar_Syntax_Subst.subst s
                                           goal.FStar_Tactics_Types.goal_ty
                                          in
                                       {
                                         FStar_Tactics_Types.context = env';
                                         FStar_Tactics_Types.witness =
                                           uu____4720;
                                         FStar_Tactics_Types.goal_ty =
                                           uu____4721;
                                         FStar_Tactics_Types.opts =
                                           (uu___94_4719.FStar_Tactics_Types.opts);
                                         FStar_Tactics_Types.is_guard =
                                           (uu___94_4719.FStar_Tactics_Types.is_guard)
                                       }  in
                                     [uu____4718]  in
                                   add_goals uu____4715  in
                                 bind uu____4712
                                   (fun uu____4724  ->
                                      let uu____4725 =
                                        FStar_Syntax_Util.mk_eq2
                                          (FStar_Syntax_Syntax.U_succ u) ty
                                          bv.FStar_Syntax_Syntax.sort t'
                                         in
                                      add_irrelevant_goal
                                        "binder_retype equation" e0
                                        uu____4725
                                        goal.FStar_Tactics_Types.opts))))))
  
let (norm_binder_type :
  FStar_Syntax_Embeddings.norm_step Prims.list ->
    FStar_Syntax_Syntax.binder -> Prims.unit tac)
  =
  fun s  ->
    fun b  ->
      bind cur_goal
        (fun goal  ->
           let uu____4746 = b  in
           match uu____4746 with
           | (bv,uu____4750) ->
               let uu____4751 = split_env bv goal.FStar_Tactics_Types.context
                  in
               (match uu____4751 with
                | FStar_Pervasives_Native.None  ->
                    fail
                      "binder_retype: binder is not present in environment"
                | FStar_Pervasives_Native.Some (e0,bvs) ->
                    let steps =
                      let uu____4783 =
                        FStar_TypeChecker_Normalize.tr_norm_steps s  in
                      FStar_List.append
                        [FStar_TypeChecker_Normalize.Reify;
                        FStar_TypeChecker_Normalize.UnfoldTac] uu____4783
                       in
                    let sort' =
                      normalize steps e0 bv.FStar_Syntax_Syntax.sort  in
                    let bv' =
                      let uu___95_4788 = bv  in
                      {
                        FStar_Syntax_Syntax.ppname =
                          (uu___95_4788.FStar_Syntax_Syntax.ppname);
                        FStar_Syntax_Syntax.index =
                          (uu___95_4788.FStar_Syntax_Syntax.index);
                        FStar_Syntax_Syntax.sort = sort'
                      }  in
                    let env' = push_bvs e0 (bv' :: bvs)  in
                    replace_cur
                      (let uu___96_4792 = goal  in
                       {
                         FStar_Tactics_Types.context = env';
                         FStar_Tactics_Types.witness =
                           (uu___96_4792.FStar_Tactics_Types.witness);
                         FStar_Tactics_Types.goal_ty =
                           (uu___96_4792.FStar_Tactics_Types.goal_ty);
                         FStar_Tactics_Types.opts =
                           (uu___96_4792.FStar_Tactics_Types.opts);
                         FStar_Tactics_Types.is_guard =
                           (uu___96_4792.FStar_Tactics_Types.is_guard)
                       })))
  
let (revert : Prims.unit tac) =
  bind cur_goal
    (fun goal  ->
       let uu____4800 =
         FStar_TypeChecker_Env.pop_bv goal.FStar_Tactics_Types.context  in
       match uu____4800 with
       | FStar_Pervasives_Native.None  -> fail "Cannot revert; empty context"
       | FStar_Pervasives_Native.Some (x,env') ->
           let typ' =
             let uu____4822 =
               FStar_Syntax_Syntax.mk_Total goal.FStar_Tactics_Types.goal_ty
                in
             FStar_Syntax_Util.arrow [(x, FStar_Pervasives_Native.None)]
               uu____4822
              in
           let w' =
             FStar_Syntax_Util.abs [(x, FStar_Pervasives_Native.None)]
               goal.FStar_Tactics_Types.witness FStar_Pervasives_Native.None
              in
           replace_cur
             (let uu___97_4856 = goal  in
              {
                FStar_Tactics_Types.context = env';
                FStar_Tactics_Types.witness = w';
                FStar_Tactics_Types.goal_ty = typ';
                FStar_Tactics_Types.opts =
                  (uu___97_4856.FStar_Tactics_Types.opts);
                FStar_Tactics_Types.is_guard =
                  (uu___97_4856.FStar_Tactics_Types.is_guard)
              }))
  
let (free_in :
  FStar_Syntax_Syntax.bv -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun bv  ->
    fun t  ->
      let uu____4863 = FStar_Syntax_Free.names t  in
      FStar_Util.set_mem bv uu____4863
  
let rec (clear : FStar_Syntax_Syntax.binder -> Prims.unit tac) =
  fun b  ->
    let bv = FStar_Pervasives_Native.fst b  in
    bind cur_goal
      (fun goal  ->
         mlog
           (fun uu____4879  ->
              let uu____4880 = FStar_Syntax_Print.binder_to_string b  in
              let uu____4881 =
                let uu____4882 =
                  let uu____4883 =
                    FStar_TypeChecker_Env.all_binders
                      goal.FStar_Tactics_Types.context
                     in
                  FStar_All.pipe_right uu____4883 FStar_List.length  in
                FStar_All.pipe_right uu____4882 FStar_Util.string_of_int  in
              FStar_Util.print2 "Clear of (%s), env has %s binders\n"
                uu____4880 uu____4881)
           (fun uu____4894  ->
              let uu____4895 = split_env bv goal.FStar_Tactics_Types.context
                 in
              match uu____4895 with
              | FStar_Pervasives_Native.None  ->
                  fail "Cannot clear; binder not in environment"
              | FStar_Pervasives_Native.Some (e',bvs) ->
                  let rec check bvs1 =
                    match bvs1 with
                    | [] -> ret ()
                    | bv'::bvs2 ->
                        let uu____4940 =
                          free_in bv bv'.FStar_Syntax_Syntax.sort  in
                        if uu____4940
                        then
                          let uu____4943 =
                            let uu____4944 =
                              FStar_Syntax_Print.bv_to_string bv'  in
                            FStar_Util.format1
                              "Cannot clear; binder present in the type of %s"
                              uu____4944
                             in
                          fail uu____4943
                        else check bvs2
                     in
                  let uu____4946 =
                    free_in bv goal.FStar_Tactics_Types.goal_ty  in
                  if uu____4946
                  then fail "Cannot clear; binder present in goal"
                  else
                    (let uu____4950 = check bvs  in
                     bind uu____4950
                       (fun uu____4956  ->
                          let env' = push_bvs e' bvs  in
                          let uu____4958 =
                            new_uvar "clear.witness" env'
                              goal.FStar_Tactics_Types.goal_ty
                             in
                          bind uu____4958
                            (fun ut  ->
                               let uu____4964 =
                                 do_unify goal.FStar_Tactics_Types.context
                                   goal.FStar_Tactics_Types.witness ut
                                  in
                               if uu____4964
                               then
                                 replace_cur
                                   (let uu___98_4969 = goal  in
                                    {
                                      FStar_Tactics_Types.context = env';
                                      FStar_Tactics_Types.witness = ut;
                                      FStar_Tactics_Types.goal_ty =
                                        (uu___98_4969.FStar_Tactics_Types.goal_ty);
                                      FStar_Tactics_Types.opts =
                                        (uu___98_4969.FStar_Tactics_Types.opts);
                                      FStar_Tactics_Types.is_guard =
                                        (uu___98_4969.FStar_Tactics_Types.is_guard)
                                    })
                               else
                                 fail
                                   "Cannot clear; binder appears in witness")))))
  
let (clear_top : Prims.unit tac) =
  bind cur_goal
    (fun goal  ->
       let uu____4978 =
         FStar_TypeChecker_Env.pop_bv goal.FStar_Tactics_Types.context  in
       match uu____4978 with
       | FStar_Pervasives_Native.None  -> fail "Cannot clear; empty context"
       | FStar_Pervasives_Native.Some (x,uu____4992) ->
           let uu____4997 = FStar_Syntax_Syntax.mk_binder x  in
           clear uu____4997)
  
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
           let uu___99_5013 = g  in
           {
             FStar_Tactics_Types.context = ctx';
             FStar_Tactics_Types.witness =
               (uu___99_5013.FStar_Tactics_Types.witness);
             FStar_Tactics_Types.goal_ty =
               (uu___99_5013.FStar_Tactics_Types.goal_ty);
             FStar_Tactics_Types.opts =
               (uu___99_5013.FStar_Tactics_Types.opts);
             FStar_Tactics_Types.is_guard =
               (uu___99_5013.FStar_Tactics_Types.is_guard)
           }  in
         bind dismiss (fun uu____5015  -> add_goals [g']))
  
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
           let uu___100_5031 = g  in
           {
             FStar_Tactics_Types.context = ctx';
             FStar_Tactics_Types.witness =
               (uu___100_5031.FStar_Tactics_Types.witness);
             FStar_Tactics_Types.goal_ty =
               (uu___100_5031.FStar_Tactics_Types.goal_ty);
             FStar_Tactics_Types.opts =
               (uu___100_5031.FStar_Tactics_Types.opts);
             FStar_Tactics_Types.is_guard =
               (uu___100_5031.FStar_Tactics_Types.is_guard)
           }  in
         bind dismiss (fun uu____5033  -> add_goals [g']))
  
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
            let uu____5065 = FStar_Syntax_Subst.compress t  in
            uu____5065.FStar_Syntax_Syntax.n  in
          let uu____5068 =
            if d = FStar_Tactics_Types.TopDown
            then
              f env
                (let uu___102_5074 = t  in
                 {
                   FStar_Syntax_Syntax.n = tn;
                   FStar_Syntax_Syntax.pos =
                     (uu___102_5074.FStar_Syntax_Syntax.pos);
                   FStar_Syntax_Syntax.vars =
                     (uu___102_5074.FStar_Syntax_Syntax.vars)
                 })
            else ret t  in
          bind uu____5068
            (fun t1  ->
               let tn1 =
                 let uu____5082 =
                   let uu____5083 = FStar_Syntax_Subst.compress t1  in
                   uu____5083.FStar_Syntax_Syntax.n  in
                 match uu____5082 with
                 | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
                     let ff = tac_fold_env d f env  in
                     let uu____5115 = ff hd1  in
                     bind uu____5115
                       (fun hd2  ->
                          let fa uu____5135 =
                            match uu____5135 with
                            | (a,q) ->
                                let uu____5148 = ff a  in
                                bind uu____5148 (fun a1  -> ret (a1, q))
                             in
                          let uu____5161 = mapM fa args  in
                          bind uu____5161
                            (fun args1  ->
                               ret (FStar_Syntax_Syntax.Tm_app (hd2, args1))))
                 | FStar_Syntax_Syntax.Tm_abs (bs,t2,k) ->
                     let uu____5221 = FStar_Syntax_Subst.open_term bs t2  in
                     (match uu____5221 with
                      | (bs1,t') ->
                          let uu____5230 =
                            let uu____5233 =
                              FStar_TypeChecker_Env.push_binders env bs1  in
                            tac_fold_env d f uu____5233 t'  in
                          bind uu____5230
                            (fun t''  ->
                               let uu____5237 =
                                 let uu____5238 =
                                   let uu____5255 =
                                     FStar_Syntax_Subst.close_binders bs1  in
                                   let uu____5256 =
                                     FStar_Syntax_Subst.close bs1 t''  in
                                   (uu____5255, uu____5256, k)  in
                                 FStar_Syntax_Syntax.Tm_abs uu____5238  in
                               ret uu____5237))
                 | FStar_Syntax_Syntax.Tm_arrow (bs,k) -> ret tn
                 | uu____5277 -> ret tn  in
               bind tn1
                 (fun tn2  ->
                    let t' =
                      let uu___101_5284 = t1  in
                      {
                        FStar_Syntax_Syntax.n = tn2;
                        FStar_Syntax_Syntax.pos =
                          (uu___101_5284.FStar_Syntax_Syntax.pos);
                        FStar_Syntax_Syntax.vars =
                          (uu___101_5284.FStar_Syntax_Syntax.vars)
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
            let uu____5313 = FStar_TypeChecker_TcTerm.tc_term env t  in
            match uu____5313 with
            | (t1,lcomp,g) ->
                let uu____5325 =
                  (let uu____5328 =
                     FStar_Syntax_Util.is_pure_or_ghost_lcomp lcomp  in
                   Prims.op_Negation uu____5328) ||
                    (let uu____5330 = FStar_TypeChecker_Rel.is_trivial g  in
                     Prims.op_Negation uu____5330)
                   in
                if uu____5325
                then ret t1
                else
                  (let rewrite_eq =
                     let typ = lcomp.FStar_Syntax_Syntax.res_typ  in
                     let uu____5340 = new_uvar "pointwise_rec" env typ  in
                     bind uu____5340
                       (fun ut  ->
                          log ps
                            (fun uu____5351  ->
                               let uu____5352 =
                                 FStar_Syntax_Print.term_to_string t1  in
                               let uu____5353 =
                                 FStar_Syntax_Print.term_to_string ut  in
                               FStar_Util.print2
                                 "Pointwise_rec: making equality\n\t%s ==\n\t%s\n"
                                 uu____5352 uu____5353);
                          (let uu____5354 =
                             let uu____5357 =
                               let uu____5358 =
                                 FStar_TypeChecker_TcTerm.universe_of env typ
                                  in
                               FStar_Syntax_Util.mk_eq2 uu____5358 typ t1 ut
                                in
                             add_irrelevant_goal "pointwise_rec equation" env
                               uu____5357 opts
                              in
                           bind uu____5354
                             (fun uu____5361  ->
                                let uu____5362 =
                                  bind tau
                                    (fun uu____5368  ->
                                       let ut1 =
                                         FStar_TypeChecker_Normalize.reduce_uvar_solutions
                                           env ut
                                          in
                                       log ps
                                         (fun uu____5374  ->
                                            let uu____5375 =
                                              FStar_Syntax_Print.term_to_string
                                                t1
                                               in
                                            let uu____5376 =
                                              FStar_Syntax_Print.term_to_string
                                                ut1
                                               in
                                            FStar_Util.print2
                                              "Pointwise_rec: succeeded rewriting\n\t%s to\n\t%s\n"
                                              uu____5375 uu____5376);
                                       ret ut1)
                                   in
                                focus uu____5362)))
                      in
                   let uu____5377 = trytac' rewrite_eq  in
                   bind uu____5377
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
           let uu____5419 =
             match ps.FStar_Tactics_Types.goals with
             | g::gs -> (g, gs)
             | [] -> failwith "Pointwise: no goals"  in
           match uu____5419 with
           | (g,gs) ->
               let gt1 = g.FStar_Tactics_Types.goal_ty  in
               (log ps
                  (fun uu____5456  ->
                     let uu____5457 = FStar_Syntax_Print.term_to_string gt1
                        in
                     FStar_Util.print1 "Pointwise starting with %s\n"
                       uu____5457);
                bind dismiss_all
                  (fun uu____5460  ->
                     let uu____5461 =
                       tac_fold_env d
                         (pointwise_rec ps tau g.FStar_Tactics_Types.opts)
                         g.FStar_Tactics_Types.context gt1
                        in
                     bind uu____5461
                       (fun gt'  ->
                          log ps
                            (fun uu____5471  ->
                               let uu____5472 =
                                 FStar_Syntax_Print.term_to_string gt'  in
                               FStar_Util.print1
                                 "Pointwise seems to have succeded with %s\n"
                                 uu____5472);
                          (let uu____5473 = push_goals gs  in
                           bind uu____5473
                             (fun uu____5477  ->
                                add_goals
                                  [(let uu___103_5479 = g  in
                                    {
                                      FStar_Tactics_Types.context =
                                        (uu___103_5479.FStar_Tactics_Types.context);
                                      FStar_Tactics_Types.witness =
                                        (uu___103_5479.FStar_Tactics_Types.witness);
                                      FStar_Tactics_Types.goal_ty = gt';
                                      FStar_Tactics_Types.opts =
                                        (uu___103_5479.FStar_Tactics_Types.opts);
                                      FStar_Tactics_Types.is_guard =
                                        (uu___103_5479.FStar_Tactics_Types.is_guard)
                                    })]))))))
  
let (trefl : Prims.unit tac) =
  bind cur_goal
    (fun g  ->
       let uu____5501 =
         FStar_Syntax_Util.un_squash g.FStar_Tactics_Types.goal_ty  in
       match uu____5501 with
       | FStar_Pervasives_Native.Some t ->
           let uu____5513 = FStar_Syntax_Util.head_and_args' t  in
           (match uu____5513 with
            | (hd1,args) ->
                let uu____5546 =
                  let uu____5559 =
                    let uu____5560 = FStar_Syntax_Util.un_uinst hd1  in
                    uu____5560.FStar_Syntax_Syntax.n  in
                  (uu____5559, args)  in
                (match uu____5546 with
                 | (FStar_Syntax_Syntax.Tm_fvar
                    fv,uu____5574::(l,uu____5576)::(r,uu____5578)::[]) when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.eq2_lid
                     ->
                     let uu____5625 =
                       let uu____5626 =
                         do_unify g.FStar_Tactics_Types.context l r  in
                       Prims.op_Negation uu____5626  in
                     if uu____5625
                     then
                       let uu____5629 = tts g.FStar_Tactics_Types.context l
                          in
                       let uu____5630 = tts g.FStar_Tactics_Types.context r
                          in
                       fail2 "trefl: not a trivial equality (%s vs %s)"
                         uu____5629 uu____5630
                     else solve g FStar_Syntax_Util.exp_unit
                 | (hd2,uu____5633) ->
                     let uu____5650 = tts g.FStar_Tactics_Types.context t  in
                     fail1 "trefl: not an equality (%s)" uu____5650))
       | FStar_Pervasives_Native.None  -> fail "not an irrelevant goal")
  
let (dup : Prims.unit tac) =
  bind cur_goal
    (fun g  ->
       let uu____5660 =
         new_uvar "dup" g.FStar_Tactics_Types.context
           g.FStar_Tactics_Types.goal_ty
          in
       bind uu____5660
         (fun u  ->
            let g' =
              let uu___104_5667 = g  in
              {
                FStar_Tactics_Types.context =
                  (uu___104_5667.FStar_Tactics_Types.context);
                FStar_Tactics_Types.witness = u;
                FStar_Tactics_Types.goal_ty =
                  (uu___104_5667.FStar_Tactics_Types.goal_ty);
                FStar_Tactics_Types.opts =
                  (uu___104_5667.FStar_Tactics_Types.opts);
                FStar_Tactics_Types.is_guard =
                  (uu___104_5667.FStar_Tactics_Types.is_guard)
              }  in
            bind dismiss
              (fun uu____5670  ->
                 let uu____5671 =
                   let uu____5674 =
                     let uu____5675 =
                       FStar_TypeChecker_TcTerm.universe_of
                         g.FStar_Tactics_Types.context
                         g.FStar_Tactics_Types.goal_ty
                        in
                     FStar_Syntax_Util.mk_eq2 uu____5675
                       g.FStar_Tactics_Types.goal_ty u
                       g.FStar_Tactics_Types.witness
                      in
                   add_irrelevant_goal "dup equation"
                     g.FStar_Tactics_Types.context uu____5674
                     g.FStar_Tactics_Types.opts
                    in
                 bind uu____5671
                   (fun uu____5678  ->
                      let uu____5679 = add_goals [g']  in
                      bind uu____5679 (fun uu____5683  -> ret ())))))
  
let (flip : Prims.unit tac) =
  bind get
    (fun ps  ->
       match ps.FStar_Tactics_Types.goals with
       | g1::g2::gs ->
           set
             (let uu___105_5702 = ps  in
              {
                FStar_Tactics_Types.main_context =
                  (uu___105_5702.FStar_Tactics_Types.main_context);
                FStar_Tactics_Types.main_goal =
                  (uu___105_5702.FStar_Tactics_Types.main_goal);
                FStar_Tactics_Types.all_implicits =
                  (uu___105_5702.FStar_Tactics_Types.all_implicits);
                FStar_Tactics_Types.goals = (g2 :: g1 :: gs);
                FStar_Tactics_Types.smt_goals =
                  (uu___105_5702.FStar_Tactics_Types.smt_goals);
                FStar_Tactics_Types.depth =
                  (uu___105_5702.FStar_Tactics_Types.depth);
                FStar_Tactics_Types.__dump =
                  (uu___105_5702.FStar_Tactics_Types.__dump);
                FStar_Tactics_Types.psc =
                  (uu___105_5702.FStar_Tactics_Types.psc);
                FStar_Tactics_Types.entry_range =
                  (uu___105_5702.FStar_Tactics_Types.entry_range)
              })
       | uu____5703 -> fail "flip: less than 2 goals")
  
let (later : Prims.unit tac) =
  bind get
    (fun ps  ->
       match ps.FStar_Tactics_Types.goals with
       | [] -> ret ()
       | g::gs ->
           set
             (let uu___106_5720 = ps  in
              {
                FStar_Tactics_Types.main_context =
                  (uu___106_5720.FStar_Tactics_Types.main_context);
                FStar_Tactics_Types.main_goal =
                  (uu___106_5720.FStar_Tactics_Types.main_goal);
                FStar_Tactics_Types.all_implicits =
                  (uu___106_5720.FStar_Tactics_Types.all_implicits);
                FStar_Tactics_Types.goals = (FStar_List.append gs [g]);
                FStar_Tactics_Types.smt_goals =
                  (uu___106_5720.FStar_Tactics_Types.smt_goals);
                FStar_Tactics_Types.depth =
                  (uu___106_5720.FStar_Tactics_Types.depth);
                FStar_Tactics_Types.__dump =
                  (uu___106_5720.FStar_Tactics_Types.__dump);
                FStar_Tactics_Types.psc =
                  (uu___106_5720.FStar_Tactics_Types.psc);
                FStar_Tactics_Types.entry_range =
                  (uu___106_5720.FStar_Tactics_Types.entry_range)
              }))
  
let (qed : Prims.unit tac) =
  bind get
    (fun ps  ->
       match ps.FStar_Tactics_Types.goals with
       | [] -> ret ()
       | uu____5729 -> fail "Not done!")
  
let (cases :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 tac)
  =
  fun t  ->
    let uu____5747 =
      bind cur_goal
        (fun g  ->
           let uu____5761 = __tc g.FStar_Tactics_Types.context t  in
           bind uu____5761
             (fun uu____5797  ->
                match uu____5797 with
                | (t1,typ,guard) ->
                    let uu____5813 = FStar_Syntax_Util.head_and_args typ  in
                    (match uu____5813 with
                     | (hd1,args) ->
                         let uu____5856 =
                           let uu____5869 =
                             let uu____5870 = FStar_Syntax_Util.un_uinst hd1
                                in
                             uu____5870.FStar_Syntax_Syntax.n  in
                           (uu____5869, args)  in
                         (match uu____5856 with
                          | (FStar_Syntax_Syntax.Tm_fvar
                             fv,(p,uu____5889)::(q,uu____5891)::[]) when
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
                                let uu___107_5929 = g  in
                                let uu____5930 =
                                  FStar_TypeChecker_Env.push_bv
                                    g.FStar_Tactics_Types.context v_p
                                   in
                                {
                                  FStar_Tactics_Types.context = uu____5930;
                                  FStar_Tactics_Types.witness =
                                    (uu___107_5929.FStar_Tactics_Types.witness);
                                  FStar_Tactics_Types.goal_ty =
                                    (uu___107_5929.FStar_Tactics_Types.goal_ty);
                                  FStar_Tactics_Types.opts =
                                    (uu___107_5929.FStar_Tactics_Types.opts);
                                  FStar_Tactics_Types.is_guard =
                                    (uu___107_5929.FStar_Tactics_Types.is_guard)
                                }  in
                              let g2 =
                                let uu___108_5932 = g  in
                                let uu____5933 =
                                  FStar_TypeChecker_Env.push_bv
                                    g.FStar_Tactics_Types.context v_q
                                   in
                                {
                                  FStar_Tactics_Types.context = uu____5933;
                                  FStar_Tactics_Types.witness =
                                    (uu___108_5932.FStar_Tactics_Types.witness);
                                  FStar_Tactics_Types.goal_ty =
                                    (uu___108_5932.FStar_Tactics_Types.goal_ty);
                                  FStar_Tactics_Types.opts =
                                    (uu___108_5932.FStar_Tactics_Types.opts);
                                  FStar_Tactics_Types.is_guard =
                                    (uu___108_5932.FStar_Tactics_Types.is_guard)
                                }  in
                              bind dismiss
                                (fun uu____5940  ->
                                   let uu____5941 = add_goals [g1; g2]  in
                                   bind uu____5941
                                     (fun uu____5950  ->
                                        let uu____5951 =
                                          let uu____5956 =
                                            FStar_Syntax_Syntax.bv_to_name
                                              v_p
                                             in
                                          let uu____5957 =
                                            FStar_Syntax_Syntax.bv_to_name
                                              v_q
                                             in
                                          (uu____5956, uu____5957)  in
                                        ret uu____5951))
                          | uu____5962 ->
                              let uu____5975 =
                                tts g.FStar_Tactics_Types.context typ  in
                              fail1 "Not a disjunction: %s" uu____5975))))
       in
    FStar_All.pipe_left (wrap_err "cases") uu____5747
  
let (set_options : Prims.string -> Prims.unit tac) =
  fun s  ->
    bind cur_goal
      (fun g  ->
         FStar_Options.push ();
         (let uu____6013 = FStar_Util.smap_copy g.FStar_Tactics_Types.opts
             in
          FStar_Options.set uu____6013);
         (let res = FStar_Options.set_options FStar_Options.Set s  in
          let opts' = FStar_Options.peek ()  in
          FStar_Options.pop ();
          (match res with
           | FStar_Getopt.Success  ->
               let g' =
                 let uu___109_6020 = g  in
                 {
                   FStar_Tactics_Types.context =
                     (uu___109_6020.FStar_Tactics_Types.context);
                   FStar_Tactics_Types.witness =
                     (uu___109_6020.FStar_Tactics_Types.witness);
                   FStar_Tactics_Types.goal_ty =
                     (uu___109_6020.FStar_Tactics_Types.goal_ty);
                   FStar_Tactics_Types.opts = opts';
                   FStar_Tactics_Types.is_guard =
                     (uu___109_6020.FStar_Tactics_Types.is_guard)
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
      let uu____6064 =
        bind cur_goal
          (fun goal  ->
             let env =
               FStar_TypeChecker_Env.set_expected_typ
                 goal.FStar_Tactics_Types.context ty
                in
             let uu____6072 = __tc env tm  in
             bind uu____6072
               (fun uu____6092  ->
                  match uu____6092 with
                  | (tm1,typ,guard) ->
                      (FStar_TypeChecker_Rel.force_trivial_guard env guard;
                       ret tm1)))
         in
      FStar_All.pipe_left (wrap_err "unquote") uu____6064
  
let (uvar_env :
  env ->
    FStar_Syntax_Syntax.typ FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.term tac)
  =
  fun env  ->
    fun ty  ->
      let uu____6123 =
        match ty with
        | FStar_Pervasives_Native.Some ty1 -> ret ty1
        | FStar_Pervasives_Native.None  ->
            let uu____6129 =
              let uu____6130 = FStar_Syntax_Util.type_u ()  in
              FStar_All.pipe_left FStar_Pervasives_Native.fst uu____6130  in
            new_uvar "uvar_env.2" env uu____6129
         in
      bind uu____6123
        (fun typ  ->
           let uu____6142 = new_uvar "uvar_env" env typ  in
           bind uu____6142 (fun t  -> ret t))
  
let (unshelve : FStar_Syntax_Syntax.term -> Prims.unit tac) =
  fun t  ->
    let uu____6154 =
      bind cur_goal
        (fun goal  ->
           let uu____6160 = __tc goal.FStar_Tactics_Types.context t  in
           bind uu____6160
             (fun uu____6180  ->
                match uu____6180 with
                | (t1,typ,guard) ->
                    let uu____6192 =
                      must_trivial goal.FStar_Tactics_Types.context guard  in
                    bind uu____6192
                      (fun uu____6197  ->
                         let uu____6198 =
                           let uu____6201 =
                             let uu___110_6202 = goal  in
                             let uu____6203 =
                               bnorm goal.FStar_Tactics_Types.context t1  in
                             let uu____6204 =
                               bnorm goal.FStar_Tactics_Types.context typ  in
                             {
                               FStar_Tactics_Types.context =
                                 (uu___110_6202.FStar_Tactics_Types.context);
                               FStar_Tactics_Types.witness = uu____6203;
                               FStar_Tactics_Types.goal_ty = uu____6204;
                               FStar_Tactics_Types.opts =
                                 (uu___110_6202.FStar_Tactics_Types.opts);
                               FStar_Tactics_Types.is_guard = false
                             }  in
                           [uu____6201]  in
                         add_goals uu____6198)))
       in
    FStar_All.pipe_left (wrap_err "unshelve") uu____6154
  
let (unify :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool tac) =
  fun t1  ->
    fun t2  ->
      bind get
        (fun ps  ->
           let uu____6222 =
             do_unify ps.FStar_Tactics_Types.main_context t1 t2  in
           ret uu____6222)
  
let (launch_process :
  Prims.string -> Prims.string -> Prims.string -> Prims.string tac) =
  fun prog  ->
    fun args  ->
      fun input  ->
        bind idtac
          (fun uu____6239  ->
             let uu____6240 = FStar_Options.unsafe_tactic_exec ()  in
             if uu____6240
             then
               let s =
                 FStar_Util.launch_process true "tactic_launch" prog args
                   input (fun uu____6246  -> fun uu____6247  -> false)
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
      let uu____6263 =
        FStar_TypeChecker_Util.new_implicit_var "proofstate_of_goal_ty"
          typ.FStar_Syntax_Syntax.pos env typ
         in
      match uu____6263 with
      | (u,uu____6281,g_u) ->
          let g =
            let uu____6296 = FStar_Options.peek ()  in
            {
              FStar_Tactics_Types.context = env;
              FStar_Tactics_Types.witness = u;
              FStar_Tactics_Types.goal_ty = typ;
              FStar_Tactics_Types.opts = uu____6296;
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
      let uu____6307 = goal_of_goal_ty env typ  in
      match uu____6307 with
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
  