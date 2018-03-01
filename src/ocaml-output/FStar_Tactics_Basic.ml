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
         let uu___63_917 = p  in
         let uu____918 = FStar_List.tl p.FStar_Tactics_Types.goals  in
         {
           FStar_Tactics_Types.main_context =
             (uu___63_917.FStar_Tactics_Types.main_context);
           FStar_Tactics_Types.main_goal =
             (uu___63_917.FStar_Tactics_Types.main_goal);
           FStar_Tactics_Types.all_implicits =
             (uu___63_917.FStar_Tactics_Types.all_implicits);
           FStar_Tactics_Types.goals = uu____918;
           FStar_Tactics_Types.smt_goals =
             (uu___63_917.FStar_Tactics_Types.smt_goals);
           FStar_Tactics_Types.depth =
             (uu___63_917.FStar_Tactics_Types.depth);
           FStar_Tactics_Types.__dump =
             (uu___63_917.FStar_Tactics_Types.__dump);
           FStar_Tactics_Types.psc = (uu___63_917.FStar_Tactics_Types.psc);
           FStar_Tactics_Types.entry_range =
             (uu___63_917.FStar_Tactics_Types.entry_range)
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
         (let uu___64_945 = p  in
          {
            FStar_Tactics_Types.main_context =
              (uu___64_945.FStar_Tactics_Types.main_context);
            FStar_Tactics_Types.main_goal =
              (uu___64_945.FStar_Tactics_Types.main_goal);
            FStar_Tactics_Types.all_implicits =
              (uu___64_945.FStar_Tactics_Types.all_implicits);
            FStar_Tactics_Types.goals = [];
            FStar_Tactics_Types.smt_goals =
              (uu___64_945.FStar_Tactics_Types.smt_goals);
            FStar_Tactics_Types.depth =
              (uu___64_945.FStar_Tactics_Types.depth);
            FStar_Tactics_Types.__dump =
              (uu___64_945.FStar_Tactics_Types.__dump);
            FStar_Tactics_Types.psc = (uu___64_945.FStar_Tactics_Types.psc);
            FStar_Tactics_Types.entry_range =
              (uu___64_945.FStar_Tactics_Types.entry_range)
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
           (let uu___65_1084 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___65_1084.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___65_1084.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___65_1084.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (FStar_List.append gs p.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___65_1084.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___65_1084.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___65_1084.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___65_1084.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___65_1084.FStar_Tactics_Types.entry_range)
            }))
  
let (add_smt_goals : FStar_Tactics_Types.goal Prims.list -> Prims.unit tac) =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___66_1102 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___66_1102.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___66_1102.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___66_1102.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___66_1102.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (FStar_List.append gs p.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___66_1102.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___66_1102.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___66_1102.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___66_1102.FStar_Tactics_Types.entry_range)
            }))
  
let (push_goals : FStar_Tactics_Types.goal Prims.list -> Prims.unit tac) =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___67_1120 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___67_1120.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___67_1120.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___67_1120.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (FStar_List.append p.FStar_Tactics_Types.goals gs);
              FStar_Tactics_Types.smt_goals =
                (uu___67_1120.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___67_1120.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___67_1120.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___67_1120.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___67_1120.FStar_Tactics_Types.entry_range)
            }))
  
let (push_smt_goals : FStar_Tactics_Types.goal Prims.list -> Prims.unit tac)
  =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___68_1138 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___68_1138.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___68_1138.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___68_1138.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___68_1138.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (FStar_List.append p.FStar_Tactics_Types.smt_goals gs);
              FStar_Tactics_Types.depth =
                (uu___68_1138.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___68_1138.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___68_1138.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___68_1138.FStar_Tactics_Types.entry_range)
            }))
  
let (replace_cur : FStar_Tactics_Types.goal -> Prims.unit tac) =
  fun g  -> bind dismiss (fun uu____1147  -> add_goals [g]) 
let (add_implicits : implicits -> Prims.unit tac) =
  fun i  ->
    bind get
      (fun p  ->
         set
           (let uu___69_1159 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___69_1159.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___69_1159.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (FStar_List.append i p.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___69_1159.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___69_1159.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___69_1159.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___69_1159.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___69_1159.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___69_1159.FStar_Tactics_Types.entry_range)
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
           with | e1 -> fail "not typeable")
  
let (must_trivial : env -> FStar_TypeChecker_Env.guard_t -> Prims.unit tac) =
  fun e  ->
    fun g  ->
      try
        let uu____1408 =
          let uu____1409 =
            let uu____1410 = FStar_TypeChecker_Rel.discharge_guard_no_smt e g
               in
            FStar_All.pipe_left FStar_TypeChecker_Rel.is_trivial uu____1410
             in
          Prims.op_Negation uu____1409  in
        if uu____1408 then fail "got non-trivial guard" else ret ()
      with | uu____1419 -> fail "got non-trivial guard"
  
let (tc : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.typ tac) =
  fun t  ->
    let uu____1427 =
      bind cur_goal
        (fun goal  ->
           let uu____1433 = __tc goal.FStar_Tactics_Types.context t  in
           bind uu____1433
             (fun uu____1453  ->
                match uu____1453 with
                | (t1,typ,guard) ->
                    let uu____1465 =
                      must_trivial goal.FStar_Tactics_Types.context guard  in
                    bind uu____1465 (fun uu____1469  -> ret typ)))
       in
    FStar_All.pipe_left (wrap_err "tc") uu____1427
  
let (add_irrelevant_goal :
  Prims.string ->
    env ->
      FStar_Syntax_Syntax.typ -> FStar_Options.optionstate -> Prims.unit tac)
  =
  fun reason  ->
    fun env  ->
      fun phi  ->
        fun opts  ->
          let uu____1490 = mk_irrelevant_goal reason env phi opts  in
          bind uu____1490 (fun goal  -> add_goals [goal])
  
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
       let uu____1512 =
         istrivial goal.FStar_Tactics_Types.context
           goal.FStar_Tactics_Types.goal_ty
          in
       if uu____1512
       then solve goal FStar_Syntax_Util.exp_unit
       else
         (let uu____1516 =
            tts goal.FStar_Tactics_Types.context
              goal.FStar_Tactics_Types.goal_ty
             in
          fail1 "Not a trivial goal: %s" uu____1516))
  
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
          let uu____1533 =
            let uu____1534 = FStar_TypeChecker_Rel.simplify_guard e g  in
            uu____1534.FStar_TypeChecker_Env.guard_f  in
          match uu____1533 with
          | FStar_TypeChecker_Common.Trivial  -> ret ()
          | FStar_TypeChecker_Common.NonTrivial f ->
              let uu____1538 = istrivial e f  in
              if uu____1538
              then ret ()
              else
                (let uu____1542 = mk_irrelevant_goal reason e f opts  in
                 bind uu____1542
                   (fun goal  ->
                      let goal1 =
                        let uu___74_1549 = goal  in
                        {
                          FStar_Tactics_Types.context =
                            (uu___74_1549.FStar_Tactics_Types.context);
                          FStar_Tactics_Types.witness =
                            (uu___74_1549.FStar_Tactics_Types.witness);
                          FStar_Tactics_Types.goal_ty =
                            (uu___74_1549.FStar_Tactics_Types.goal_ty);
                          FStar_Tactics_Types.opts =
                            (uu___74_1549.FStar_Tactics_Types.opts);
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
          let uu____1570 =
            let uu____1571 = FStar_TypeChecker_Rel.simplify_guard e g  in
            uu____1571.FStar_TypeChecker_Env.guard_f  in
          match uu____1570 with
          | FStar_TypeChecker_Common.Trivial  ->
              ret FStar_Pervasives_Native.None
          | FStar_TypeChecker_Common.NonTrivial f ->
              let uu____1579 = istrivial e f  in
              if uu____1579
              then ret FStar_Pervasives_Native.None
              else
                (let uu____1587 = mk_irrelevant_goal reason e f opts  in
                 bind uu____1587
                   (fun goal  ->
                      ret
                        (FStar_Pervasives_Native.Some
                           (let uu___75_1597 = goal  in
                            {
                              FStar_Tactics_Types.context =
                                (uu___75_1597.FStar_Tactics_Types.context);
                              FStar_Tactics_Types.witness =
                                (uu___75_1597.FStar_Tactics_Types.witness);
                              FStar_Tactics_Types.goal_ty =
                                (uu___75_1597.FStar_Tactics_Types.goal_ty);
                              FStar_Tactics_Types.opts =
                                (uu___75_1597.FStar_Tactics_Types.opts);
                              FStar_Tactics_Types.is_guard = true
                            }))))
  
let (smt : Prims.unit tac) =
  bind cur_goal
    (fun g  ->
       let uu____1605 = is_irrelevant g  in
       if uu____1605
       then bind dismiss (fun uu____1609  -> add_smt_goals [g])
       else
         (let uu____1611 =
            tts g.FStar_Tactics_Types.context g.FStar_Tactics_Types.goal_ty
             in
          fail1 "goal is not irrelevant: cannot dispatch to smt (%s)"
            uu____1611))
  
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
             let uu____1652 =
               try
                 let uu____1686 =
                   let uu____1695 = FStar_BigInt.to_int_fs n1  in
                   FStar_List.splitAt uu____1695 p.FStar_Tactics_Types.goals
                    in
                 ret uu____1686
               with | uu____1717 -> fail "divide: not enough goals"  in
             bind uu____1652
               (fun uu____1744  ->
                  match uu____1744 with
                  | (lgs,rgs) ->
                      let lp =
                        let uu___76_1770 = p  in
                        {
                          FStar_Tactics_Types.main_context =
                            (uu___76_1770.FStar_Tactics_Types.main_context);
                          FStar_Tactics_Types.main_goal =
                            (uu___76_1770.FStar_Tactics_Types.main_goal);
                          FStar_Tactics_Types.all_implicits =
                            (uu___76_1770.FStar_Tactics_Types.all_implicits);
                          FStar_Tactics_Types.goals = lgs;
                          FStar_Tactics_Types.smt_goals = [];
                          FStar_Tactics_Types.depth =
                            (uu___76_1770.FStar_Tactics_Types.depth);
                          FStar_Tactics_Types.__dump =
                            (uu___76_1770.FStar_Tactics_Types.__dump);
                          FStar_Tactics_Types.psc =
                            (uu___76_1770.FStar_Tactics_Types.psc);
                          FStar_Tactics_Types.entry_range =
                            (uu___76_1770.FStar_Tactics_Types.entry_range)
                        }  in
                      let rp =
                        let uu___77_1772 = p  in
                        {
                          FStar_Tactics_Types.main_context =
                            (uu___77_1772.FStar_Tactics_Types.main_context);
                          FStar_Tactics_Types.main_goal =
                            (uu___77_1772.FStar_Tactics_Types.main_goal);
                          FStar_Tactics_Types.all_implicits =
                            (uu___77_1772.FStar_Tactics_Types.all_implicits);
                          FStar_Tactics_Types.goals = rgs;
                          FStar_Tactics_Types.smt_goals = [];
                          FStar_Tactics_Types.depth =
                            (uu___77_1772.FStar_Tactics_Types.depth);
                          FStar_Tactics_Types.__dump =
                            (uu___77_1772.FStar_Tactics_Types.__dump);
                          FStar_Tactics_Types.psc =
                            (uu___77_1772.FStar_Tactics_Types.psc);
                          FStar_Tactics_Types.entry_range =
                            (uu___77_1772.FStar_Tactics_Types.entry_range)
                        }  in
                      let uu____1773 = set lp  in
                      bind uu____1773
                        (fun uu____1781  ->
                           bind l
                             (fun a  ->
                                bind get
                                  (fun lp'  ->
                                     let uu____1795 = set rp  in
                                     bind uu____1795
                                       (fun uu____1803  ->
                                          bind r
                                            (fun b  ->
                                               bind get
                                                 (fun rp'  ->
                                                    let p' =
                                                      let uu___78_1819 = p
                                                         in
                                                      {
                                                        FStar_Tactics_Types.main_context
                                                          =
                                                          (uu___78_1819.FStar_Tactics_Types.main_context);
                                                        FStar_Tactics_Types.main_goal
                                                          =
                                                          (uu___78_1819.FStar_Tactics_Types.main_goal);
                                                        FStar_Tactics_Types.all_implicits
                                                          =
                                                          (uu___78_1819.FStar_Tactics_Types.all_implicits);
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
                                                          (uu___78_1819.FStar_Tactics_Types.depth);
                                                        FStar_Tactics_Types.__dump
                                                          =
                                                          (uu___78_1819.FStar_Tactics_Types.__dump);
                                                        FStar_Tactics_Types.psc
                                                          =
                                                          (uu___78_1819.FStar_Tactics_Types.psc);
                                                        FStar_Tactics_Types.entry_range
                                                          =
                                                          (uu___78_1819.FStar_Tactics_Types.entry_range)
                                                      }  in
                                                    let uu____1820 = set p'
                                                       in
                                                    bind uu____1820
                                                      (fun uu____1828  ->
                                                         ret (a, b))))))))))
  
let focus : 'a . 'a tac -> 'a tac =
  fun f  ->
    let uu____1846 = divide FStar_BigInt.one f idtac  in
    bind uu____1846
      (fun uu____1859  -> match uu____1859 with | (a,()) -> ret a)
  
let rec map : 'a . 'a tac -> 'a Prims.list tac =
  fun tau  ->
    bind get
      (fun p  ->
         match p.FStar_Tactics_Types.goals with
         | [] -> ret []
         | uu____1893::uu____1894 ->
             let uu____1897 =
               let uu____1906 = map tau  in
               divide FStar_BigInt.one tau uu____1906  in
             bind uu____1897
               (fun uu____1924  ->
                  match uu____1924 with | (h,t) -> ret (h :: t)))
  
let (seq : Prims.unit tac -> Prims.unit tac -> Prims.unit tac) =
  fun t1  ->
    fun t2  ->
      let uu____1961 =
        bind t1
          (fun uu____1966  ->
             let uu____1967 = map t2  in
             bind uu____1967 (fun uu____1975  -> ret ()))
         in
      focus uu____1961
  
let (intro : FStar_Syntax_Syntax.binder tac) =
  bind cur_goal
    (fun goal  ->
       let uu____1988 =
         FStar_Syntax_Util.arrow_one goal.FStar_Tactics_Types.goal_ty  in
       match uu____1988 with
       | FStar_Pervasives_Native.Some (b,c) ->
           let uu____2003 =
             let uu____2004 = FStar_Syntax_Util.is_total_comp c  in
             Prims.op_Negation uu____2004  in
           if uu____2003
           then fail "Codomain is effectful"
           else
             (let env' =
                FStar_TypeChecker_Env.push_binders
                  goal.FStar_Tactics_Types.context [b]
                 in
              let typ' = comp_to_typ c  in
              let uu____2010 = new_uvar "intro" env' typ'  in
              bind uu____2010
                (fun u  ->
                   let uu____2017 =
                     let uu____2018 =
                       FStar_Syntax_Util.abs [b] u
                         FStar_Pervasives_Native.None
                        in
                     trysolve goal uu____2018  in
                   if uu____2017
                   then
                     let uu____2021 =
                       let uu____2024 =
                         let uu___81_2025 = goal  in
                         let uu____2026 = bnorm env' u  in
                         let uu____2027 = bnorm env' typ'  in
                         {
                           FStar_Tactics_Types.context = env';
                           FStar_Tactics_Types.witness = uu____2026;
                           FStar_Tactics_Types.goal_ty = uu____2027;
                           FStar_Tactics_Types.opts =
                             (uu___81_2025.FStar_Tactics_Types.opts);
                           FStar_Tactics_Types.is_guard =
                             (uu___81_2025.FStar_Tactics_Types.is_guard)
                         }  in
                       replace_cur uu____2024  in
                     bind uu____2021 (fun uu____2029  -> ret b)
                   else fail "intro: unification failed"))
       | FStar_Pervasives_Native.None  ->
           let uu____2035 =
             tts goal.FStar_Tactics_Types.context
               goal.FStar_Tactics_Types.goal_ty
              in
           fail1 "intro: goal is not an arrow (%s)" uu____2035)
  
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
       (let uu____2062 =
          FStar_Syntax_Util.arrow_one goal.FStar_Tactics_Types.goal_ty  in
        match uu____2062 with
        | FStar_Pervasives_Native.Some (b,c) ->
            let uu____2081 =
              let uu____2082 = FStar_Syntax_Util.is_total_comp c  in
              Prims.op_Negation uu____2082  in
            if uu____2081
            then fail "Codomain is effectful"
            else
              (let bv =
                 FStar_Syntax_Syntax.gen_bv "__recf"
                   FStar_Pervasives_Native.None
                   goal.FStar_Tactics_Types.goal_ty
                  in
               let bs =
                 let uu____2098 = FStar_Syntax_Syntax.mk_binder bv  in
                 [uu____2098; b]  in
               let env' =
                 FStar_TypeChecker_Env.push_binders
                   goal.FStar_Tactics_Types.context bs
                  in
               let uu____2100 =
                 let uu____2103 = comp_to_typ c  in
                 new_uvar "intro_rec" env' uu____2103  in
               bind uu____2100
                 (fun u  ->
                    let lb =
                      let uu____2119 =
                        FStar_Syntax_Util.abs [b] u
                          FStar_Pervasives_Native.None
                         in
                      FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl bv) []
                        goal.FStar_Tactics_Types.goal_ty
                        FStar_Parser_Const.effect_Tot_lid uu____2119 []
                       in
                    let body = FStar_Syntax_Syntax.bv_to_name bv  in
                    let uu____2125 =
                      FStar_Syntax_Subst.close_let_rec [lb] body  in
                    match uu____2125 with
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
                          let uu____2162 =
                            let uu____2165 =
                              let uu___82_2166 = goal  in
                              let uu____2167 = bnorm env' u  in
                              let uu____2168 =
                                let uu____2169 = comp_to_typ c  in
                                bnorm env' uu____2169  in
                              {
                                FStar_Tactics_Types.context = env';
                                FStar_Tactics_Types.witness = uu____2167;
                                FStar_Tactics_Types.goal_ty = uu____2168;
                                FStar_Tactics_Types.opts =
                                  (uu___82_2166.FStar_Tactics_Types.opts);
                                FStar_Tactics_Types.is_guard =
                                  (uu___82_2166.FStar_Tactics_Types.is_guard)
                              }  in
                            replace_cur uu____2165  in
                          bind uu____2162
                            (fun uu____2176  ->
                               let uu____2177 =
                                 let uu____2182 =
                                   FStar_Syntax_Syntax.mk_binder bv  in
                                 (uu____2182, b)  in
                               ret uu____2177)
                        else fail "intro_rec: unification failed"))
        | FStar_Pervasives_Native.None  ->
            let uu____2196 =
              tts goal.FStar_Tactics_Types.context
                goal.FStar_Tactics_Types.goal_ty
               in
            fail1 "intro_rec: goal is not an arrow (%s)" uu____2196))
  
let (norm : FStar_Syntax_Embeddings.norm_step Prims.list -> Prims.unit tac) =
  fun s  ->
    bind cur_goal
      (fun goal  ->
         mlog
           (fun uu____2216  ->
              let uu____2217 =
                FStar_Syntax_Print.term_to_string
                  goal.FStar_Tactics_Types.witness
                 in
              FStar_Util.print1 "norm: witness = %s\n" uu____2217)
           (fun uu____2222  ->
              let steps =
                let uu____2226 = FStar_TypeChecker_Normalize.tr_norm_steps s
                   in
                FStar_List.append
                  [FStar_TypeChecker_Normalize.Reify;
                  FStar_TypeChecker_Normalize.UnfoldTac] uu____2226
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
                (let uu___83_2233 = goal  in
                 {
                   FStar_Tactics_Types.context =
                     (uu___83_2233.FStar_Tactics_Types.context);
                   FStar_Tactics_Types.witness = w;
                   FStar_Tactics_Types.goal_ty = t;
                   FStar_Tactics_Types.opts =
                     (uu___83_2233.FStar_Tactics_Types.opts);
                   FStar_Tactics_Types.is_guard =
                     (uu___83_2233.FStar_Tactics_Types.is_guard)
                 })))
  
let (norm_term_env :
  env ->
    FStar_Syntax_Embeddings.norm_step Prims.list ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac)
  =
  fun e  ->
    fun s  ->
      fun t  ->
        let uu____2251 =
          mlog
            (fun uu____2256  ->
               let uu____2257 = FStar_Syntax_Print.term_to_string t  in
               FStar_Util.print1 "norm_term: tm = %s\n" uu____2257)
            (fun uu____2259  ->
               bind get
                 (fun ps  ->
                    let uu____2263 = __tc e t  in
                    bind uu____2263
                      (fun uu____2285  ->
                         match uu____2285 with
                         | (t1,uu____2295,guard) ->
                             (FStar_TypeChecker_Rel.force_trivial_guard e
                                guard;
                              (let steps =
                                 let uu____2301 =
                                   FStar_TypeChecker_Normalize.tr_norm_steps
                                     s
                                    in
                                 FStar_List.append
                                   [FStar_TypeChecker_Normalize.Reify;
                                   FStar_TypeChecker_Normalize.UnfoldTac]
                                   uu____2301
                                  in
                               let t2 =
                                 normalize steps
                                   ps.FStar_Tactics_Types.main_context t1
                                  in
                               ret t2)))))
           in
        FStar_All.pipe_left (wrap_err "norm_term") uu____2251
  
let (refine_intro : Prims.unit tac) =
  let uu____2313 =
    bind cur_goal
      (fun g  ->
         let uu____2320 =
           FStar_TypeChecker_Rel.base_and_refinement
             g.FStar_Tactics_Types.context g.FStar_Tactics_Types.goal_ty
            in
         match uu____2320 with
         | (uu____2333,FStar_Pervasives_Native.None ) ->
             fail "not a refinement"
         | (t,FStar_Pervasives_Native.Some (bv,phi)) ->
             let g1 =
               let uu___84_2358 = g  in
               {
                 FStar_Tactics_Types.context =
                   (uu___84_2358.FStar_Tactics_Types.context);
                 FStar_Tactics_Types.witness =
                   (uu___84_2358.FStar_Tactics_Types.witness);
                 FStar_Tactics_Types.goal_ty = t;
                 FStar_Tactics_Types.opts =
                   (uu___84_2358.FStar_Tactics_Types.opts);
                 FStar_Tactics_Types.is_guard =
                   (uu___84_2358.FStar_Tactics_Types.is_guard)
               }  in
             let uu____2359 =
               let uu____2364 =
                 let uu____2369 =
                   let uu____2370 = FStar_Syntax_Syntax.mk_binder bv  in
                   [uu____2370]  in
                 FStar_Syntax_Subst.open_term uu____2369 phi  in
               match uu____2364 with
               | (bvs,phi1) ->
                   let uu____2377 =
                     let uu____2378 = FStar_List.hd bvs  in
                     FStar_Pervasives_Native.fst uu____2378  in
                   (uu____2377, phi1)
                in
             (match uu____2359 with
              | (bv1,phi1) ->
                  let uu____2391 =
                    let uu____2394 =
                      FStar_Syntax_Subst.subst
                        [FStar_Syntax_Syntax.NT
                           (bv1, (g.FStar_Tactics_Types.witness))] phi1
                       in
                    mk_irrelevant_goal "refine_intro refinement"
                      g.FStar_Tactics_Types.context uu____2394
                      g.FStar_Tactics_Types.opts
                     in
                  bind uu____2391
                    (fun g2  ->
                       bind dismiss (fun uu____2398  -> add_goals [g1; g2]))))
     in
  FStar_All.pipe_left (wrap_err "refine_intro") uu____2313 
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
             let uu____2422 = __tc env t  in
             bind uu____2422
               (fun uu____2442  ->
                  match uu____2442 with
                  | (t1,typ,guard) ->
                      let uu____2454 =
                        if force_guard
                        then
                          must_trivial goal.FStar_Tactics_Types.context guard
                        else
                          add_goal_from_guard "__exact typing"
                            goal.FStar_Tactics_Types.context guard
                            goal.FStar_Tactics_Types.opts
                         in
                      bind uu____2454
                        (fun uu____2461  ->
                           mlog
                             (fun uu____2465  ->
                                let uu____2466 =
                                  tts goal.FStar_Tactics_Types.context typ
                                   in
                                let uu____2467 =
                                  tts goal.FStar_Tactics_Types.context
                                    goal.FStar_Tactics_Types.goal_ty
                                   in
                                FStar_Util.print2
                                  "exact: unifying %s and %s\n" uu____2466
                                  uu____2467)
                             (fun uu____2470  ->
                                let uu____2471 =
                                  do_unify goal.FStar_Tactics_Types.context
                                    typ goal.FStar_Tactics_Types.goal_ty
                                   in
                                if uu____2471
                                then solve goal t1
                                else
                                  (let uu____2475 =
                                     tts goal.FStar_Tactics_Types.context t1
                                      in
                                   let uu____2476 =
                                     tts goal.FStar_Tactics_Types.context typ
                                      in
                                   let uu____2477 =
                                     tts goal.FStar_Tactics_Types.context
                                       goal.FStar_Tactics_Types.goal_ty
                                      in
                                   let uu____2478 =
                                     tts goal.FStar_Tactics_Types.context
                                       goal.FStar_Tactics_Types.witness
                                      in
                                   fail4
                                     "%s : %s does not exactly solve the goal %s (witness = %s)"
                                     uu____2475 uu____2476 uu____2477
                                     uu____2478)))))
  
let (t_exact :
  Prims.bool -> Prims.bool -> FStar_Syntax_Syntax.term -> Prims.unit tac) =
  fun set_expected_typ1  ->
    fun force_guard  ->
      fun tm  ->
        let uu____2492 =
          mlog
            (fun uu____2497  ->
               let uu____2498 = FStar_Syntax_Print.term_to_string tm  in
               FStar_Util.print1 "t_exact: tm = %s\n" uu____2498)
            (fun uu____2501  ->
               let uu____2502 =
                 let uu____2509 =
                   __exact_now set_expected_typ1 force_guard tm  in
                 trytac' uu____2509  in
               bind uu____2502
                 (fun uu___58_2518  ->
                    match uu___58_2518 with
                    | FStar_Util.Inr r -> ret ()
                    | FStar_Util.Inl e ->
                        let uu____2527 =
                          let uu____2534 =
                            let uu____2537 =
                              norm [FStar_Syntax_Embeddings.Delta]  in
                            bind uu____2537
                              (fun uu____2541  ->
                                 bind refine_intro
                                   (fun uu____2543  ->
                                      __exact_now set_expected_typ1
                                        force_guard tm))
                             in
                          trytac' uu____2534  in
                        bind uu____2527
                          (fun uu___57_2550  ->
                             match uu___57_2550 with
                             | FStar_Util.Inr r -> ret ()
                             | FStar_Util.Inl uu____2558 -> fail e)))
           in
        FStar_All.pipe_left (wrap_err "exact") uu____2492
  
let (uvar_free_in_goal :
  FStar_Syntax_Syntax.uvar -> FStar_Tactics_Types.goal -> Prims.bool) =
  fun u  ->
    fun g  ->
      if g.FStar_Tactics_Types.is_guard
      then false
      else
        (let free_uvars =
           let uu____2573 =
             let uu____2580 =
               FStar_Syntax_Free.uvars g.FStar_Tactics_Types.goal_ty  in
             FStar_Util.set_elements uu____2580  in
           FStar_List.map FStar_Pervasives_Native.fst uu____2573  in
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
          let uu____2640 = f x  in
          bind uu____2640
            (fun y  ->
               let uu____2648 = mapM f xs  in
               bind uu____2648 (fun ys  -> ret (y :: ys)))
  
exception NoUnif 
let (uu___is_NoUnif : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with | NoUnif  -> true | uu____2666 -> false
  
let rec (__apply :
  Prims.bool ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.typ -> Prims.unit tac)
  =
  fun uopt  ->
    fun tm  ->
      fun typ  ->
        bind cur_goal
          (fun goal  ->
             let uu____2683 =
               let uu____2688 = t_exact false true tm  in trytac uu____2688
                in
             bind uu____2683
               (fun uu___59_2695  ->
                  match uu___59_2695 with
                  | FStar_Pervasives_Native.Some r -> ret ()
                  | FStar_Pervasives_Native.None  ->
                      let uu____2701 = FStar_Syntax_Util.arrow_one typ  in
                      (match uu____2701 with
                       | FStar_Pervasives_Native.None  ->
                           FStar_Exn.raise NoUnif
                       | FStar_Pervasives_Native.Some ((bv,aq),c) ->
                           mlog
                             (fun uu____2733  ->
                                let uu____2734 =
                                  FStar_Syntax_Print.binder_to_string
                                    (bv, aq)
                                   in
                                FStar_Util.print1
                                  "__apply: pushing binder %s\n" uu____2734)
                             (fun uu____2737  ->
                                let uu____2738 =
                                  let uu____2739 =
                                    FStar_Syntax_Util.is_total_comp c  in
                                  Prims.op_Negation uu____2739  in
                                if uu____2738
                                then fail "apply: not total codomain"
                                else
                                  (let uu____2743 =
                                     new_uvar "apply"
                                       goal.FStar_Tactics_Types.context
                                       bv.FStar_Syntax_Syntax.sort
                                      in
                                   bind uu____2743
                                     (fun u  ->
                                        let tm' =
                                          FStar_Syntax_Syntax.mk_Tm_app tm
                                            [(u, aq)]
                                            FStar_Pervasives_Native.None
                                            (goal.FStar_Tactics_Types.context).FStar_TypeChecker_Env.range
                                           in
                                        let typ' =
                                          let uu____2763 = comp_to_typ c  in
                                          FStar_All.pipe_left
                                            (FStar_Syntax_Subst.subst
                                               [FStar_Syntax_Syntax.NT
                                                  (bv, u)]) uu____2763
                                           in
                                        let uu____2764 =
                                          __apply uopt tm' typ'  in
                                        bind uu____2764
                                          (fun uu____2772  ->
                                             let u1 =
                                               bnorm
                                                 goal.FStar_Tactics_Types.context
                                                 u
                                                in
                                             let uu____2774 =
                                               let uu____2775 =
                                                 let uu____2778 =
                                                   let uu____2779 =
                                                     FStar_Syntax_Util.head_and_args
                                                       u1
                                                      in
                                                   FStar_Pervasives_Native.fst
                                                     uu____2779
                                                    in
                                                 FStar_Syntax_Subst.compress
                                                   uu____2778
                                                  in
                                               uu____2775.FStar_Syntax_Syntax.n
                                                in
                                             match uu____2774 with
                                             | FStar_Syntax_Syntax.Tm_uvar
                                                 (uvar,uu____2807) ->
                                                 bind get
                                                   (fun ps  ->
                                                      let uu____2835 =
                                                        uopt &&
                                                          (uvar_free uvar ps)
                                                         in
                                                      if uu____2835
                                                      then ret ()
                                                      else
                                                        (let uu____2839 =
                                                           let uu____2842 =
                                                             let uu___85_2843
                                                               = goal  in
                                                             let uu____2844 =
                                                               bnorm
                                                                 goal.FStar_Tactics_Types.context
                                                                 u1
                                                                in
                                                             let uu____2845 =
                                                               bnorm
                                                                 goal.FStar_Tactics_Types.context
                                                                 bv.FStar_Syntax_Syntax.sort
                                                                in
                                                             {
                                                               FStar_Tactics_Types.context
                                                                 =
                                                                 (uu___85_2843.FStar_Tactics_Types.context);
                                                               FStar_Tactics_Types.witness
                                                                 = uu____2844;
                                                               FStar_Tactics_Types.goal_ty
                                                                 = uu____2845;
                                                               FStar_Tactics_Types.opts
                                                                 =
                                                                 (uu___85_2843.FStar_Tactics_Types.opts);
                                                               FStar_Tactics_Types.is_guard
                                                                 = false
                                                             }  in
                                                           [uu____2842]  in
                                                         add_goals uu____2839))
                                             | t -> ret ())))))))
  
let try_unif : 'a . 'a tac -> 'a tac -> 'a tac =
  fun t  ->
    fun t'  -> mk_tac (fun ps  -> try run t ps with | NoUnif  -> run t' ps)
  
let (apply : Prims.bool -> FStar_Syntax_Syntax.term -> Prims.unit tac) =
  fun uopt  ->
    fun tm  ->
      let uu____2891 =
        mlog
          (fun uu____2896  ->
             let uu____2897 = FStar_Syntax_Print.term_to_string tm  in
             FStar_Util.print1 "apply: tm = %s\n" uu____2897)
          (fun uu____2899  ->
             bind cur_goal
               (fun goal  ->
                  let uu____2903 = __tc goal.FStar_Tactics_Types.context tm
                     in
                  bind uu____2903
                    (fun uu____2924  ->
                       match uu____2924 with
                       | (tm1,typ,guard) ->
                           let uu____2936 =
                             let uu____2939 =
                               let uu____2942 = __apply uopt tm1 typ  in
                               bind uu____2942
                                 (fun uu____2946  ->
                                    add_goal_from_guard "apply guard"
                                      goal.FStar_Tactics_Types.context guard
                                      goal.FStar_Tactics_Types.opts)
                                in
                             focus uu____2939  in
                           let uu____2947 =
                             let uu____2950 =
                               tts goal.FStar_Tactics_Types.context tm1  in
                             let uu____2951 =
                               tts goal.FStar_Tactics_Types.context typ  in
                             let uu____2952 =
                               tts goal.FStar_Tactics_Types.context
                                 goal.FStar_Tactics_Types.goal_ty
                                in
                             fail3
                               "Cannot instantiate %s (of type %s) to match goal (%s)"
                               uu____2950 uu____2951 uu____2952
                              in
                           try_unif uu____2936 uu____2947)))
         in
      FStar_All.pipe_left (wrap_err "apply") uu____2891
  
let (apply_lemma : FStar_Syntax_Syntax.term -> Prims.unit tac) =
  fun tm  ->
    let uu____2964 =
      let uu____2967 =
        mlog
          (fun uu____2972  ->
             let uu____2973 = FStar_Syntax_Print.term_to_string tm  in
             FStar_Util.print1 "apply_lemma: tm = %s\n" uu____2973)
          (fun uu____2976  ->
             let is_unit_t t =
               let uu____2981 =
                 let uu____2982 = FStar_Syntax_Subst.compress t  in
                 uu____2982.FStar_Syntax_Syntax.n  in
               match uu____2981 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.unit_lid
                   -> true
               | uu____2986 -> false  in
             bind cur_goal
               (fun goal  ->
                  let uu____2990 = __tc goal.FStar_Tactics_Types.context tm
                     in
                  bind uu____2990
                    (fun uu____3012  ->
                       match uu____3012 with
                       | (tm1,t,guard) ->
                           let uu____3024 =
                             FStar_Syntax_Util.arrow_formals_comp t  in
                           (match uu____3024 with
                            | (bs,comp) ->
                                if
                                  Prims.op_Negation
                                    (FStar_Syntax_Util.is_lemma_comp comp)
                                then fail "not a lemma"
                                else
                                  (let uu____3054 =
                                     FStar_List.fold_left
                                       (fun uu____3100  ->
                                          fun uu____3101  ->
                                            match (uu____3100, uu____3101)
                                            with
                                            | ((uvs,guard1,subst1),(b,aq)) ->
                                                let b_t =
                                                  FStar_Syntax_Subst.subst
                                                    subst1
                                                    b.FStar_Syntax_Syntax.sort
                                                   in
                                                let uu____3204 =
                                                  is_unit_t b_t  in
                                                if uu____3204
                                                then
                                                  (((FStar_Syntax_Util.exp_unit,
                                                      aq) :: uvs), guard1,
                                                    ((FStar_Syntax_Syntax.NT
                                                        (b,
                                                          FStar_Syntax_Util.exp_unit))
                                                    :: subst1))
                                                else
                                                  (let uu____3242 =
                                                     FStar_TypeChecker_Util.new_implicit_var
                                                       "apply_lemma"
                                                       (goal.FStar_Tactics_Types.goal_ty).FStar_Syntax_Syntax.pos
                                                       goal.FStar_Tactics_Types.context
                                                       b_t
                                                      in
                                                   match uu____3242 with
                                                   | (u,uu____3272,g_u) ->
                                                       let uu____3286 =
                                                         FStar_TypeChecker_Rel.conj_guard
                                                           guard1 g_u
                                                          in
                                                       (((u, aq) :: uvs),
                                                         uu____3286,
                                                         ((FStar_Syntax_Syntax.NT
                                                             (b, u)) ::
                                                         subst1))))
                                       ([], guard, []) bs
                                      in
                                   match uu____3054 with
                                   | (uvs,implicits,subst1) ->
                                       let uvs1 = FStar_List.rev uvs  in
                                       let comp1 =
                                         FStar_Syntax_Subst.subst_comp subst1
                                           comp
                                          in
                                       let uu____3356 =
                                         let uu____3365 =
                                           let uu____3374 =
                                             FStar_Syntax_Util.comp_to_comp_typ
                                               comp1
                                              in
                                           uu____3374.FStar_Syntax_Syntax.effect_args
                                            in
                                         match uu____3365 with
                                         | pre::post::uu____3385 ->
                                             ((FStar_Pervasives_Native.fst
                                                 pre),
                                               (FStar_Pervasives_Native.fst
                                                  post))
                                         | uu____3426 ->
                                             failwith
                                               "apply_lemma: impossible: not a lemma"
                                          in
                                       (match uu____3356 with
                                        | (pre,post) ->
                                            let post1 =
                                              let uu____3458 =
                                                let uu____3467 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    FStar_Syntax_Util.exp_unit
                                                   in
                                                [uu____3467]  in
                                              FStar_Syntax_Util.mk_app post
                                                uu____3458
                                               in
                                            let uu____3468 =
                                              let uu____3469 =
                                                let uu____3470 =
                                                  FStar_Syntax_Util.mk_squash
                                                    FStar_Syntax_Syntax.U_zero
                                                    post1
                                                   in
                                                do_unify
                                                  goal.FStar_Tactics_Types.context
                                                  uu____3470
                                                  goal.FStar_Tactics_Types.goal_ty
                                                 in
                                              Prims.op_Negation uu____3469
                                               in
                                            if uu____3468
                                            then
                                              let uu____3473 =
                                                tts
                                                  goal.FStar_Tactics_Types.context
                                                  tm1
                                                 in
                                              let uu____3474 =
                                                let uu____3475 =
                                                  FStar_Syntax_Util.mk_squash
                                                    FStar_Syntax_Syntax.U_zero
                                                    post1
                                                   in
                                                tts
                                                  goal.FStar_Tactics_Types.context
                                                  uu____3475
                                                 in
                                              let uu____3476 =
                                                tts
                                                  goal.FStar_Tactics_Types.context
                                                  goal.FStar_Tactics_Types.goal_ty
                                                 in
                                              fail3
                                                "Cannot instantiate lemma %s (with postcondition: %s) to match goal (%s)"
                                                uu____3473 uu____3474
                                                uu____3476
                                            else
                                              (let uu____3478 =
                                                 add_implicits
                                                   implicits.FStar_TypeChecker_Env.implicits
                                                  in
                                               bind uu____3478
                                                 (fun uu____3483  ->
                                                    let uu____3484 =
                                                      solve goal
                                                        FStar_Syntax_Util.exp_unit
                                                       in
                                                    bind uu____3484
                                                      (fun uu____3492  ->
                                                         let is_free_uvar uv
                                                           t1 =
                                                           let free_uvars =
                                                             let uu____3503 =
                                                               let uu____3510
                                                                 =
                                                                 FStar_Syntax_Free.uvars
                                                                   t1
                                                                  in
                                                               FStar_Util.set_elements
                                                                 uu____3510
                                                                in
                                                             FStar_List.map
                                                               FStar_Pervasives_Native.fst
                                                               uu____3503
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
                                                           let uu____3551 =
                                                             FStar_Syntax_Util.head_and_args
                                                               t1
                                                              in
                                                           match uu____3551
                                                           with
                                                           | (hd1,uu____3567)
                                                               ->
                                                               (match 
                                                                  hd1.FStar_Syntax_Syntax.n
                                                                with
                                                                | FStar_Syntax_Syntax.Tm_uvar
                                                                    (uv,uu____3589)
                                                                    ->
                                                                    appears
                                                                    uv goals
                                                                | uu____3614
                                                                    -> false)
                                                            in
                                                         let uu____3615 =
                                                           FStar_All.pipe_right
                                                             implicits.FStar_TypeChecker_Env.implicits
                                                             (mapM
                                                                (fun
                                                                   uu____3687
                                                                    ->
                                                                   match uu____3687
                                                                   with
                                                                   | 
                                                                   (_msg,env,_uvar,term,typ,uu____3715)
                                                                    ->
                                                                    let uu____3716
                                                                    =
                                                                    FStar_Syntax_Util.head_and_args
                                                                    term  in
                                                                    (match uu____3716
                                                                    with
                                                                    | 
                                                                    (hd1,uu____3742)
                                                                    ->
                                                                    let uu____3763
                                                                    =
                                                                    let uu____3764
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    hd1  in
                                                                    uu____3764.FStar_Syntax_Syntax.n
                                                                     in
                                                                    (match uu____3763
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Tm_uvar
                                                                    uu____3777
                                                                    ->
                                                                    let uu____3794
                                                                    =
                                                                    let uu____3803
                                                                    =
                                                                    let uu____3806
                                                                    =
                                                                    let uu___88_3807
                                                                    = goal
                                                                     in
                                                                    let uu____3808
                                                                    =
                                                                    bnorm
                                                                    goal.FStar_Tactics_Types.context
                                                                    term  in
                                                                    let uu____3809
                                                                    =
                                                                    bnorm
                                                                    goal.FStar_Tactics_Types.context
                                                                    typ  in
                                                                    {
                                                                    FStar_Tactics_Types.context
                                                                    =
                                                                    (uu___88_3807.FStar_Tactics_Types.context);
                                                                    FStar_Tactics_Types.witness
                                                                    =
                                                                    uu____3808;
                                                                    FStar_Tactics_Types.goal_ty
                                                                    =
                                                                    uu____3809;
                                                                    FStar_Tactics_Types.opts
                                                                    =
                                                                    (uu___88_3807.FStar_Tactics_Types.opts);
                                                                    FStar_Tactics_Types.is_guard
                                                                    =
                                                                    (uu___88_3807.FStar_Tactics_Types.is_guard)
                                                                    }  in
                                                                    [uu____3806]
                                                                     in
                                                                    (uu____3803,
                                                                    [])  in
                                                                    ret
                                                                    uu____3794
                                                                    | 
                                                                    uu____3822
                                                                    ->
                                                                    let g_typ
                                                                    =
                                                                    let uu____3824
                                                                    =
                                                                    FStar_Options.__temp_fast_implicits
                                                                    ()  in
                                                                    if
                                                                    uu____3824
                                                                    then
                                                                    FStar_TypeChecker_TcTerm.check_type_of_well_typed_term
                                                                    false env
                                                                    term typ
                                                                    else
                                                                    (let term1
                                                                    =
                                                                    bnorm env
                                                                    term  in
                                                                    let uu____3827
                                                                    =
                                                                    let uu____3834
                                                                    =
                                                                    FStar_TypeChecker_Env.set_expected_typ
                                                                    env typ
                                                                     in
                                                                    env.FStar_TypeChecker_Env.type_of
                                                                    uu____3834
                                                                    term1  in
                                                                    match uu____3827
                                                                    with
                                                                    | 
                                                                    (uu____3835,uu____3836,g_typ)
                                                                    -> g_typ)
                                                                     in
                                                                    let uu____3838
                                                                    =
                                                                    goal_from_guard
                                                                    "apply_lemma solved arg"
                                                                    goal.FStar_Tactics_Types.context
                                                                    g_typ
                                                                    goal.FStar_Tactics_Types.opts
                                                                     in
                                                                    bind
                                                                    uu____3838
                                                                    (fun
                                                                    uu___60_3854
                                                                     ->
                                                                    match uu___60_3854
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
                                                         bind uu____3615
                                                           (fun goals_  ->
                                                              let sub_goals =
                                                                let uu____3922
                                                                  =
                                                                  FStar_List.map
                                                                    FStar_Pervasives_Native.fst
                                                                    goals_
                                                                   in
                                                                FStar_List.flatten
                                                                  uu____3922
                                                                 in
                                                              let smt_goals =
                                                                let uu____3944
                                                                  =
                                                                  FStar_List.map
                                                                    FStar_Pervasives_Native.snd
                                                                    goals_
                                                                   in
                                                                FStar_List.flatten
                                                                  uu____3944
                                                                 in
                                                              let rec filter'
                                                                a f xs =
                                                                match xs with
                                                                | [] -> []
                                                                | x::xs1 ->
                                                                    let uu____3999
                                                                    = f x xs1
                                                                     in
                                                                    if
                                                                    uu____3999
                                                                    then
                                                                    let uu____4002
                                                                    =
                                                                    filter'
                                                                    () f xs1
                                                                     in x ::
                                                                    uu____4002
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
                                                                    let uu____4016
                                                                    =
                                                                    checkone
                                                                    g.FStar_Tactics_Types.witness
                                                                    goals  in
                                                                    Prims.op_Negation
                                                                    uu____4016))
                                                                    a434 a435)
                                                                    (Obj.magic
                                                                    sub_goals))
                                                                 in
                                                              let uu____4017
                                                                =
                                                                add_goal_from_guard
                                                                  "apply_lemma guard"
                                                                  goal.FStar_Tactics_Types.context
                                                                  guard
                                                                  goal.FStar_Tactics_Types.opts
                                                                 in
                                                              bind uu____4017
                                                                (fun
                                                                   uu____4022
                                                                    ->
                                                                   let uu____4023
                                                                    =
                                                                    let uu____4026
                                                                    =
                                                                    let uu____4027
                                                                    =
                                                                    let uu____4028
                                                                    =
                                                                    FStar_Syntax_Util.mk_squash
                                                                    FStar_Syntax_Syntax.U_zero
                                                                    pre  in
                                                                    istrivial
                                                                    goal.FStar_Tactics_Types.context
                                                                    uu____4028
                                                                     in
                                                                    Prims.op_Negation
                                                                    uu____4027
                                                                     in
                                                                    if
                                                                    uu____4026
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
                                                                    uu____4023
                                                                    (fun
                                                                    uu____4034
                                                                     ->
                                                                    let uu____4035
                                                                    =
                                                                    add_smt_goals
                                                                    smt_goals
                                                                     in
                                                                    bind
                                                                    uu____4035
                                                                    (fun
                                                                    uu____4039
                                                                     ->
                                                                    add_goals
                                                                    sub_goals1)))))))))))))
         in
      focus uu____2967  in
    FStar_All.pipe_left (wrap_err "apply_lemma") uu____2964
  
let (destruct_eq' :
  FStar_Syntax_Syntax.typ ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun typ  ->
    let uu____4059 = FStar_Syntax_Util.destruct_typ_as_formula typ  in
    match uu____4059 with
    | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn
        (l,uu____4069::(e1,uu____4071)::(e2,uu____4073)::[])) when
        FStar_Ident.lid_equals l FStar_Parser_Const.eq2_lid ->
        FStar_Pervasives_Native.Some (e1, e2)
    | uu____4132 -> FStar_Pervasives_Native.None
  
let (destruct_eq :
  FStar_Syntax_Syntax.typ ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun typ  ->
    let uu____4154 = destruct_eq' typ  in
    match uu____4154 with
    | FStar_Pervasives_Native.Some t -> FStar_Pervasives_Native.Some t
    | FStar_Pervasives_Native.None  ->
        let uu____4184 = FStar_Syntax_Util.un_squash typ  in
        (match uu____4184 with
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
        let uu____4240 = FStar_TypeChecker_Env.pop_bv e1  in
        match uu____4240 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (bv',e') ->
            if FStar_Syntax_Syntax.bv_eq bvar bv'
            then FStar_Pervasives_Native.Some (e', [])
            else
              (let uu____4288 = aux e'  in
               FStar_Util.map_opt uu____4288
                 (fun uu____4312  ->
                    match uu____4312 with | (e'',bvs) -> (e'', (bv' :: bvs))))
         in
      let uu____4333 = aux e  in
      FStar_Util.map_opt uu____4333
        (fun uu____4357  ->
           match uu____4357 with | (e',bvs) -> (e', (FStar_List.rev bvs)))
  
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
          let uu____4412 = split_env b1 g.FStar_Tactics_Types.context  in
          FStar_Util.map_opt uu____4412
            (fun uu____4436  ->
               match uu____4436 with
               | (e0,bvs) ->
                   let s1 bv =
                     let uu___89_4453 = bv  in
                     let uu____4454 =
                       FStar_Syntax_Subst.subst s bv.FStar_Syntax_Syntax.sort
                        in
                     {
                       FStar_Syntax_Syntax.ppname =
                         (uu___89_4453.FStar_Syntax_Syntax.ppname);
                       FStar_Syntax_Syntax.index =
                         (uu___89_4453.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort = uu____4454
                     }  in
                   let bvs1 = FStar_List.map s1 bvs  in
                   let c = push_bvs e0 (b2 :: bvs1)  in
                   let w =
                     FStar_Syntax_Subst.subst s g.FStar_Tactics_Types.witness
                      in
                   let t =
                     FStar_Syntax_Subst.subst s g.FStar_Tactics_Types.goal_ty
                      in
                   let uu___90_4463 = g  in
                   {
                     FStar_Tactics_Types.context = c;
                     FStar_Tactics_Types.witness = w;
                     FStar_Tactics_Types.goal_ty = t;
                     FStar_Tactics_Types.opts =
                       (uu___90_4463.FStar_Tactics_Types.opts);
                     FStar_Tactics_Types.is_guard =
                       (uu___90_4463.FStar_Tactics_Types.is_guard)
                   })
  
let (rewrite : FStar_Syntax_Syntax.binder -> Prims.unit tac) =
  fun h  ->
    bind cur_goal
      (fun goal  ->
         let uu____4476 = h  in
         match uu____4476 with
         | (bv,uu____4480) ->
             mlog
               (fun uu____4484  ->
                  let uu____4485 = FStar_Syntax_Print.bv_to_string bv  in
                  let uu____4486 =
                    tts goal.FStar_Tactics_Types.context
                      bv.FStar_Syntax_Syntax.sort
                     in
                  FStar_Util.print2 "+++Rewrite %s : %s\n" uu____4485
                    uu____4486)
               (fun uu____4489  ->
                  let uu____4490 =
                    split_env bv goal.FStar_Tactics_Types.context  in
                  match uu____4490 with
                  | FStar_Pervasives_Native.None  ->
                      fail "rewrite: binder not found in environment"
                  | FStar_Pervasives_Native.Some (e0,bvs) ->
                      let uu____4519 =
                        destruct_eq bv.FStar_Syntax_Syntax.sort  in
                      (match uu____4519 with
                       | FStar_Pervasives_Native.Some (x,e) ->
                           let uu____4534 =
                             let uu____4535 = FStar_Syntax_Subst.compress x
                                in
                             uu____4535.FStar_Syntax_Syntax.n  in
                           (match uu____4534 with
                            | FStar_Syntax_Syntax.Tm_name x1 ->
                                let s = [FStar_Syntax_Syntax.NT (x1, e)]  in
                                let s1 bv1 =
                                  let uu___91_4548 = bv1  in
                                  let uu____4549 =
                                    FStar_Syntax_Subst.subst s
                                      bv1.FStar_Syntax_Syntax.sort
                                     in
                                  {
                                    FStar_Syntax_Syntax.ppname =
                                      (uu___91_4548.FStar_Syntax_Syntax.ppname);
                                    FStar_Syntax_Syntax.index =
                                      (uu___91_4548.FStar_Syntax_Syntax.index);
                                    FStar_Syntax_Syntax.sort = uu____4549
                                  }  in
                                let bvs1 = FStar_List.map s1 bvs  in
                                let uu____4555 =
                                  let uu___92_4556 = goal  in
                                  let uu____4557 = push_bvs e0 (bv :: bvs1)
                                     in
                                  let uu____4558 =
                                    FStar_Syntax_Subst.subst s
                                      goal.FStar_Tactics_Types.witness
                                     in
                                  let uu____4559 =
                                    FStar_Syntax_Subst.subst s
                                      goal.FStar_Tactics_Types.goal_ty
                                     in
                                  {
                                    FStar_Tactics_Types.context = uu____4557;
                                    FStar_Tactics_Types.witness = uu____4558;
                                    FStar_Tactics_Types.goal_ty = uu____4559;
                                    FStar_Tactics_Types.opts =
                                      (uu___92_4556.FStar_Tactics_Types.opts);
                                    FStar_Tactics_Types.is_guard =
                                      (uu___92_4556.FStar_Tactics_Types.is_guard)
                                  }  in
                                replace_cur uu____4555
                            | uu____4560 ->
                                fail
                                  "rewrite: Not an equality hypothesis with a variable on the LHS")
                       | uu____4561 ->
                           fail "rewrite: Not an equality hypothesis")))
  
let (rename_to :
  FStar_Syntax_Syntax.binder -> Prims.string -> Prims.unit tac) =
  fun b  ->
    fun s  ->
      bind cur_goal
        (fun goal  ->
           let uu____4586 = b  in
           match uu____4586 with
           | (bv,uu____4590) ->
               let bv' =
                 FStar_Syntax_Syntax.freshen_bv
                   (let uu___93_4594 = bv  in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (FStar_Ident.mk_ident
                           (s,
                             ((bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange)));
                      FStar_Syntax_Syntax.index =
                        (uu___93_4594.FStar_Syntax_Syntax.index);
                      FStar_Syntax_Syntax.sort =
                        (uu___93_4594.FStar_Syntax_Syntax.sort)
                    })
                  in
               let s1 =
                 let uu____4598 =
                   let uu____4599 =
                     let uu____4606 = FStar_Syntax_Syntax.bv_to_name bv'  in
                     (bv, uu____4606)  in
                   FStar_Syntax_Syntax.NT uu____4599  in
                 [uu____4598]  in
               let uu____4607 = subst_goal bv bv' s1 goal  in
               (match uu____4607 with
                | FStar_Pervasives_Native.None  ->
                    fail "rename_to: binder not found in environment"
                | FStar_Pervasives_Native.Some goal1 -> replace_cur goal1))
  
let (binder_retype : FStar_Syntax_Syntax.binder -> Prims.unit tac) =
  fun b  ->
    bind cur_goal
      (fun goal  ->
         let uu____4626 = b  in
         match uu____4626 with
         | (bv,uu____4630) ->
             let uu____4631 = split_env bv goal.FStar_Tactics_Types.context
                in
             (match uu____4631 with
              | FStar_Pervasives_Native.None  ->
                  fail "binder_retype: binder is not present in environment"
              | FStar_Pervasives_Native.Some (e0,bvs) ->
                  let uu____4660 = FStar_Syntax_Util.type_u ()  in
                  (match uu____4660 with
                   | (ty,u) ->
                       let uu____4669 = new_uvar "binder_retype" e0 ty  in
                       bind uu____4669
                         (fun t'  ->
                            let bv'' =
                              let uu___94_4679 = bv  in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___94_4679.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___94_4679.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = t'
                              }  in
                            let s =
                              let uu____4683 =
                                let uu____4684 =
                                  let uu____4691 =
                                    FStar_Syntax_Syntax.bv_to_name bv''  in
                                  (bv, uu____4691)  in
                                FStar_Syntax_Syntax.NT uu____4684  in
                              [uu____4683]  in
                            let bvs1 =
                              FStar_List.map
                                (fun b1  ->
                                   let uu___95_4699 = b1  in
                                   let uu____4700 =
                                     FStar_Syntax_Subst.subst s
                                       b1.FStar_Syntax_Syntax.sort
                                      in
                                   {
                                     FStar_Syntax_Syntax.ppname =
                                       (uu___95_4699.FStar_Syntax_Syntax.ppname);
                                     FStar_Syntax_Syntax.index =
                                       (uu___95_4699.FStar_Syntax_Syntax.index);
                                     FStar_Syntax_Syntax.sort = uu____4700
                                   }) bvs
                               in
                            let env' = push_bvs e0 (bv'' :: bvs1)  in
                            bind dismiss
                              (fun uu____4706  ->
                                 let uu____4707 =
                                   let uu____4710 =
                                     let uu____4713 =
                                       let uu___96_4714 = goal  in
                                       let uu____4715 =
                                         FStar_Syntax_Subst.subst s
                                           goal.FStar_Tactics_Types.witness
                                          in
                                       let uu____4716 =
                                         FStar_Syntax_Subst.subst s
                                           goal.FStar_Tactics_Types.goal_ty
                                          in
                                       {
                                         FStar_Tactics_Types.context = env';
                                         FStar_Tactics_Types.witness =
                                           uu____4715;
                                         FStar_Tactics_Types.goal_ty =
                                           uu____4716;
                                         FStar_Tactics_Types.opts =
                                           (uu___96_4714.FStar_Tactics_Types.opts);
                                         FStar_Tactics_Types.is_guard =
                                           (uu___96_4714.FStar_Tactics_Types.is_guard)
                                       }  in
                                     [uu____4713]  in
                                   add_goals uu____4710  in
                                 bind uu____4707
                                   (fun uu____4719  ->
                                      let uu____4720 =
                                        FStar_Syntax_Util.mk_eq2
                                          (FStar_Syntax_Syntax.U_succ u) ty
                                          bv.FStar_Syntax_Syntax.sort t'
                                         in
                                      add_irrelevant_goal
                                        "binder_retype equation" e0
                                        uu____4720
                                        goal.FStar_Tactics_Types.opts))))))
  
let (norm_binder_type :
  FStar_Syntax_Embeddings.norm_step Prims.list ->
    FStar_Syntax_Syntax.binder -> Prims.unit tac)
  =
  fun s  ->
    fun b  ->
      bind cur_goal
        (fun goal  ->
           let uu____4741 = b  in
           match uu____4741 with
           | (bv,uu____4745) ->
               let uu____4746 = split_env bv goal.FStar_Tactics_Types.context
                  in
               (match uu____4746 with
                | FStar_Pervasives_Native.None  ->
                    fail
                      "binder_retype: binder is not present in environment"
                | FStar_Pervasives_Native.Some (e0,bvs) ->
                    let steps =
                      let uu____4778 =
                        FStar_TypeChecker_Normalize.tr_norm_steps s  in
                      FStar_List.append
                        [FStar_TypeChecker_Normalize.Reify;
                        FStar_TypeChecker_Normalize.UnfoldTac] uu____4778
                       in
                    let sort' =
                      normalize steps e0 bv.FStar_Syntax_Syntax.sort  in
                    let bv' =
                      let uu___97_4783 = bv  in
                      {
                        FStar_Syntax_Syntax.ppname =
                          (uu___97_4783.FStar_Syntax_Syntax.ppname);
                        FStar_Syntax_Syntax.index =
                          (uu___97_4783.FStar_Syntax_Syntax.index);
                        FStar_Syntax_Syntax.sort = sort'
                      }  in
                    let env' = push_bvs e0 (bv' :: bvs)  in
                    replace_cur
                      (let uu___98_4787 = goal  in
                       {
                         FStar_Tactics_Types.context = env';
                         FStar_Tactics_Types.witness =
                           (uu___98_4787.FStar_Tactics_Types.witness);
                         FStar_Tactics_Types.goal_ty =
                           (uu___98_4787.FStar_Tactics_Types.goal_ty);
                         FStar_Tactics_Types.opts =
                           (uu___98_4787.FStar_Tactics_Types.opts);
                         FStar_Tactics_Types.is_guard =
                           (uu___98_4787.FStar_Tactics_Types.is_guard)
                       })))
  
let (revert : Prims.unit tac) =
  bind cur_goal
    (fun goal  ->
       let uu____4795 =
         FStar_TypeChecker_Env.pop_bv goal.FStar_Tactics_Types.context  in
       match uu____4795 with
       | FStar_Pervasives_Native.None  -> fail "Cannot revert; empty context"
       | FStar_Pervasives_Native.Some (x,env') ->
           let typ' =
             let uu____4817 =
               FStar_Syntax_Syntax.mk_Total goal.FStar_Tactics_Types.goal_ty
                in
             FStar_Syntax_Util.arrow [(x, FStar_Pervasives_Native.None)]
               uu____4817
              in
           let w' =
             FStar_Syntax_Util.abs [(x, FStar_Pervasives_Native.None)]
               goal.FStar_Tactics_Types.witness FStar_Pervasives_Native.None
              in
           replace_cur
             (let uu___99_4851 = goal  in
              {
                FStar_Tactics_Types.context = env';
                FStar_Tactics_Types.witness = w';
                FStar_Tactics_Types.goal_ty = typ';
                FStar_Tactics_Types.opts =
                  (uu___99_4851.FStar_Tactics_Types.opts);
                FStar_Tactics_Types.is_guard =
                  (uu___99_4851.FStar_Tactics_Types.is_guard)
              }))
  
let (free_in :
  FStar_Syntax_Syntax.bv -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun bv  ->
    fun t  ->
      let uu____4858 = FStar_Syntax_Free.names t  in
      FStar_Util.set_mem bv uu____4858
  
let rec (clear : FStar_Syntax_Syntax.binder -> Prims.unit tac) =
  fun b  ->
    let bv = FStar_Pervasives_Native.fst b  in
    bind cur_goal
      (fun goal  ->
         mlog
           (fun uu____4874  ->
              let uu____4875 = FStar_Syntax_Print.binder_to_string b  in
              let uu____4876 =
                let uu____4877 =
                  let uu____4878 =
                    FStar_TypeChecker_Env.all_binders
                      goal.FStar_Tactics_Types.context
                     in
                  FStar_All.pipe_right uu____4878 FStar_List.length  in
                FStar_All.pipe_right uu____4877 FStar_Util.string_of_int  in
              FStar_Util.print2 "Clear of (%s), env has %s binders\n"
                uu____4875 uu____4876)
           (fun uu____4889  ->
              let uu____4890 = split_env bv goal.FStar_Tactics_Types.context
                 in
              match uu____4890 with
              | FStar_Pervasives_Native.None  ->
                  fail "Cannot clear; binder not in environment"
              | FStar_Pervasives_Native.Some (e',bvs) ->
                  let rec check bvs1 =
                    match bvs1 with
                    | [] -> ret ()
                    | bv'::bvs2 ->
                        let uu____4935 =
                          free_in bv bv'.FStar_Syntax_Syntax.sort  in
                        if uu____4935
                        then
                          let uu____4938 =
                            let uu____4939 =
                              FStar_Syntax_Print.bv_to_string bv'  in
                            FStar_Util.format1
                              "Cannot clear; binder present in the type of %s"
                              uu____4939
                             in
                          fail uu____4938
                        else check bvs2
                     in
                  let uu____4941 =
                    free_in bv goal.FStar_Tactics_Types.goal_ty  in
                  if uu____4941
                  then fail "Cannot clear; binder present in goal"
                  else
                    (let uu____4945 = check bvs  in
                     bind uu____4945
                       (fun uu____4951  ->
                          let env' = push_bvs e' bvs  in
                          let uu____4953 =
                            new_uvar "clear.witness" env'
                              goal.FStar_Tactics_Types.goal_ty
                             in
                          bind uu____4953
                            (fun ut  ->
                               let uu____4959 =
                                 do_unify goal.FStar_Tactics_Types.context
                                   goal.FStar_Tactics_Types.witness ut
                                  in
                               if uu____4959
                               then
                                 replace_cur
                                   (let uu___100_4964 = goal  in
                                    {
                                      FStar_Tactics_Types.context = env';
                                      FStar_Tactics_Types.witness = ut;
                                      FStar_Tactics_Types.goal_ty =
                                        (uu___100_4964.FStar_Tactics_Types.goal_ty);
                                      FStar_Tactics_Types.opts =
                                        (uu___100_4964.FStar_Tactics_Types.opts);
                                      FStar_Tactics_Types.is_guard =
                                        (uu___100_4964.FStar_Tactics_Types.is_guard)
                                    })
                               else
                                 fail
                                   "Cannot clear; binder appears in witness")))))
  
let (clear_top : Prims.unit tac) =
  bind cur_goal
    (fun goal  ->
       let uu____4973 =
         FStar_TypeChecker_Env.pop_bv goal.FStar_Tactics_Types.context  in
       match uu____4973 with
       | FStar_Pervasives_Native.None  -> fail "Cannot clear; empty context"
       | FStar_Pervasives_Native.Some (x,uu____4987) ->
           let uu____4992 = FStar_Syntax_Syntax.mk_binder x  in
           clear uu____4992)
  
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
           let uu___101_5008 = g  in
           {
             FStar_Tactics_Types.context = ctx';
             FStar_Tactics_Types.witness =
               (uu___101_5008.FStar_Tactics_Types.witness);
             FStar_Tactics_Types.goal_ty =
               (uu___101_5008.FStar_Tactics_Types.goal_ty);
             FStar_Tactics_Types.opts =
               (uu___101_5008.FStar_Tactics_Types.opts);
             FStar_Tactics_Types.is_guard =
               (uu___101_5008.FStar_Tactics_Types.is_guard)
           }  in
         bind dismiss (fun uu____5010  -> add_goals [g']))
  
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
           let uu___102_5026 = g  in
           {
             FStar_Tactics_Types.context = ctx';
             FStar_Tactics_Types.witness =
               (uu___102_5026.FStar_Tactics_Types.witness);
             FStar_Tactics_Types.goal_ty =
               (uu___102_5026.FStar_Tactics_Types.goal_ty);
             FStar_Tactics_Types.opts =
               (uu___102_5026.FStar_Tactics_Types.opts);
             FStar_Tactics_Types.is_guard =
               (uu___102_5026.FStar_Tactics_Types.is_guard)
           }  in
         bind dismiss (fun uu____5028  -> add_goals [g']))
  
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
            let uu____5060 = FStar_Syntax_Subst.compress t  in
            uu____5060.FStar_Syntax_Syntax.n  in
          let uu____5063 =
            if d = FStar_Tactics_Types.TopDown
            then
              f env
                (let uu___104_5069 = t  in
                 {
                   FStar_Syntax_Syntax.n = tn;
                   FStar_Syntax_Syntax.pos =
                     (uu___104_5069.FStar_Syntax_Syntax.pos);
                   FStar_Syntax_Syntax.vars =
                     (uu___104_5069.FStar_Syntax_Syntax.vars)
                 })
            else ret t  in
          bind uu____5063
            (fun t1  ->
               let tn1 =
                 let uu____5077 =
                   let uu____5078 = FStar_Syntax_Subst.compress t1  in
                   uu____5078.FStar_Syntax_Syntax.n  in
                 match uu____5077 with
                 | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
                     let ff = tac_fold_env d f env  in
                     let uu____5110 = ff hd1  in
                     bind uu____5110
                       (fun hd2  ->
                          let fa uu____5130 =
                            match uu____5130 with
                            | (a,q) ->
                                let uu____5143 = ff a  in
                                bind uu____5143 (fun a1  -> ret (a1, q))
                             in
                          let uu____5156 = mapM fa args  in
                          bind uu____5156
                            (fun args1  ->
                               ret (FStar_Syntax_Syntax.Tm_app (hd2, args1))))
                 | FStar_Syntax_Syntax.Tm_abs (bs,t2,k) ->
                     let uu____5216 = FStar_Syntax_Subst.open_term bs t2  in
                     (match uu____5216 with
                      | (bs1,t') ->
                          let uu____5225 =
                            let uu____5228 =
                              FStar_TypeChecker_Env.push_binders env bs1  in
                            tac_fold_env d f uu____5228 t'  in
                          bind uu____5225
                            (fun t''  ->
                               let uu____5232 =
                                 let uu____5233 =
                                   let uu____5250 =
                                     FStar_Syntax_Subst.close_binders bs1  in
                                   let uu____5251 =
                                     FStar_Syntax_Subst.close bs1 t''  in
                                   (uu____5250, uu____5251, k)  in
                                 FStar_Syntax_Syntax.Tm_abs uu____5233  in
                               ret uu____5232))
                 | FStar_Syntax_Syntax.Tm_arrow (bs,k) -> ret tn
                 | uu____5272 -> ret tn  in
               bind tn1
                 (fun tn2  ->
                    let t' =
                      let uu___103_5279 = t1  in
                      {
                        FStar_Syntax_Syntax.n = tn2;
                        FStar_Syntax_Syntax.pos =
                          (uu___103_5279.FStar_Syntax_Syntax.pos);
                        FStar_Syntax_Syntax.vars =
                          (uu___103_5279.FStar_Syntax_Syntax.vars)
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
            let uu____5308 = FStar_TypeChecker_TcTerm.tc_term env t  in
            match uu____5308 with
            | (t1,lcomp,g) ->
                let uu____5320 =
                  (let uu____5323 =
                     FStar_Syntax_Util.is_pure_or_ghost_lcomp lcomp  in
                   Prims.op_Negation uu____5323) ||
                    (let uu____5325 = FStar_TypeChecker_Rel.is_trivial g  in
                     Prims.op_Negation uu____5325)
                   in
                if uu____5320
                then ret t1
                else
                  (let rewrite_eq =
                     let typ = lcomp.FStar_Syntax_Syntax.res_typ  in
                     let uu____5335 = new_uvar "pointwise_rec" env typ  in
                     bind uu____5335
                       (fun ut  ->
                          log ps
                            (fun uu____5346  ->
                               let uu____5347 =
                                 FStar_Syntax_Print.term_to_string t1  in
                               let uu____5348 =
                                 FStar_Syntax_Print.term_to_string ut  in
                               FStar_Util.print2
                                 "Pointwise_rec: making equality\n\t%s ==\n\t%s\n"
                                 uu____5347 uu____5348);
                          (let uu____5349 =
                             let uu____5352 =
                               let uu____5353 =
                                 FStar_TypeChecker_TcTerm.universe_of env typ
                                  in
                               FStar_Syntax_Util.mk_eq2 uu____5353 typ t1 ut
                                in
                             add_irrelevant_goal "pointwise_rec equation" env
                               uu____5352 opts
                              in
                           bind uu____5349
                             (fun uu____5356  ->
                                let uu____5357 =
                                  bind tau
                                    (fun uu____5363  ->
                                       let ut1 =
                                         FStar_TypeChecker_Normalize.reduce_uvar_solutions
                                           env ut
                                          in
                                       log ps
                                         (fun uu____5369  ->
                                            let uu____5370 =
                                              FStar_Syntax_Print.term_to_string
                                                t1
                                               in
                                            let uu____5371 =
                                              FStar_Syntax_Print.term_to_string
                                                ut1
                                               in
                                            FStar_Util.print2
                                              "Pointwise_rec: succeeded rewriting\n\t%s to\n\t%s\n"
                                              uu____5370 uu____5371);
                                       ret ut1)
                                   in
                                focus uu____5357)))
                      in
                   let uu____5372 = trytac' rewrite_eq  in
                   bind uu____5372
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
           let uu____5414 =
             match ps.FStar_Tactics_Types.goals with
             | g::gs -> (g, gs)
             | [] -> failwith "Pointwise: no goals"  in
           match uu____5414 with
           | (g,gs) ->
               let gt1 = g.FStar_Tactics_Types.goal_ty  in
               (log ps
                  (fun uu____5451  ->
                     let uu____5452 = FStar_Syntax_Print.term_to_string gt1
                        in
                     FStar_Util.print1 "Pointwise starting with %s\n"
                       uu____5452);
                bind dismiss_all
                  (fun uu____5455  ->
                     let uu____5456 =
                       tac_fold_env d
                         (pointwise_rec ps tau g.FStar_Tactics_Types.opts)
                         g.FStar_Tactics_Types.context gt1
                        in
                     bind uu____5456
                       (fun gt'  ->
                          log ps
                            (fun uu____5466  ->
                               let uu____5467 =
                                 FStar_Syntax_Print.term_to_string gt'  in
                               FStar_Util.print1
                                 "Pointwise seems to have succeded with %s\n"
                                 uu____5467);
                          (let uu____5468 = push_goals gs  in
                           bind uu____5468
                             (fun uu____5472  ->
                                add_goals
                                  [(let uu___105_5474 = g  in
                                    {
                                      FStar_Tactics_Types.context =
                                        (uu___105_5474.FStar_Tactics_Types.context);
                                      FStar_Tactics_Types.witness =
                                        (uu___105_5474.FStar_Tactics_Types.witness);
                                      FStar_Tactics_Types.goal_ty = gt';
                                      FStar_Tactics_Types.opts =
                                        (uu___105_5474.FStar_Tactics_Types.opts);
                                      FStar_Tactics_Types.is_guard =
                                        (uu___105_5474.FStar_Tactics_Types.is_guard)
                                    })]))))))
  
let (trefl : Prims.unit tac) =
  bind cur_goal
    (fun g  ->
       let uu____5496 =
         FStar_Syntax_Util.un_squash g.FStar_Tactics_Types.goal_ty  in
       match uu____5496 with
       | FStar_Pervasives_Native.Some t ->
           let uu____5508 = FStar_Syntax_Util.head_and_args' t  in
           (match uu____5508 with
            | (hd1,args) ->
                let uu____5541 =
                  let uu____5554 =
                    let uu____5555 = FStar_Syntax_Util.un_uinst hd1  in
                    uu____5555.FStar_Syntax_Syntax.n  in
                  (uu____5554, args)  in
                (match uu____5541 with
                 | (FStar_Syntax_Syntax.Tm_fvar
                    fv,uu____5569::(l,uu____5571)::(r,uu____5573)::[]) when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.eq2_lid
                     ->
                     let uu____5620 =
                       let uu____5621 =
                         do_unify g.FStar_Tactics_Types.context l r  in
                       Prims.op_Negation uu____5621  in
                     if uu____5620
                     then
                       let uu____5624 = tts g.FStar_Tactics_Types.context l
                          in
                       let uu____5625 = tts g.FStar_Tactics_Types.context r
                          in
                       fail2 "trefl: not a trivial equality (%s vs %s)"
                         uu____5624 uu____5625
                     else solve g FStar_Syntax_Util.exp_unit
                 | (hd2,uu____5628) ->
                     let uu____5645 = tts g.FStar_Tactics_Types.context t  in
                     fail1 "trefl: not an equality (%s)" uu____5645))
       | FStar_Pervasives_Native.None  -> fail "not an irrelevant goal")
  
let (dup : Prims.unit tac) =
  bind cur_goal
    (fun g  ->
       let uu____5655 =
         new_uvar "dup" g.FStar_Tactics_Types.context
           g.FStar_Tactics_Types.goal_ty
          in
       bind uu____5655
         (fun u  ->
            let g' =
              let uu___106_5662 = g  in
              {
                FStar_Tactics_Types.context =
                  (uu___106_5662.FStar_Tactics_Types.context);
                FStar_Tactics_Types.witness = u;
                FStar_Tactics_Types.goal_ty =
                  (uu___106_5662.FStar_Tactics_Types.goal_ty);
                FStar_Tactics_Types.opts =
                  (uu___106_5662.FStar_Tactics_Types.opts);
                FStar_Tactics_Types.is_guard =
                  (uu___106_5662.FStar_Tactics_Types.is_guard)
              }  in
            bind dismiss
              (fun uu____5665  ->
                 let uu____5666 =
                   let uu____5669 =
                     let uu____5670 =
                       FStar_TypeChecker_TcTerm.universe_of
                         g.FStar_Tactics_Types.context
                         g.FStar_Tactics_Types.goal_ty
                        in
                     FStar_Syntax_Util.mk_eq2 uu____5670
                       g.FStar_Tactics_Types.goal_ty u
                       g.FStar_Tactics_Types.witness
                      in
                   add_irrelevant_goal "dup equation"
                     g.FStar_Tactics_Types.context uu____5669
                     g.FStar_Tactics_Types.opts
                    in
                 bind uu____5666
                   (fun uu____5673  ->
                      let uu____5674 = add_goals [g']  in
                      bind uu____5674 (fun uu____5678  -> ret ())))))
  
let (flip : Prims.unit tac) =
  bind get
    (fun ps  ->
       match ps.FStar_Tactics_Types.goals with
       | g1::g2::gs ->
           set
             (let uu___107_5697 = ps  in
              {
                FStar_Tactics_Types.main_context =
                  (uu___107_5697.FStar_Tactics_Types.main_context);
                FStar_Tactics_Types.main_goal =
                  (uu___107_5697.FStar_Tactics_Types.main_goal);
                FStar_Tactics_Types.all_implicits =
                  (uu___107_5697.FStar_Tactics_Types.all_implicits);
                FStar_Tactics_Types.goals = (g2 :: g1 :: gs);
                FStar_Tactics_Types.smt_goals =
                  (uu___107_5697.FStar_Tactics_Types.smt_goals);
                FStar_Tactics_Types.depth =
                  (uu___107_5697.FStar_Tactics_Types.depth);
                FStar_Tactics_Types.__dump =
                  (uu___107_5697.FStar_Tactics_Types.__dump);
                FStar_Tactics_Types.psc =
                  (uu___107_5697.FStar_Tactics_Types.psc);
                FStar_Tactics_Types.entry_range =
                  (uu___107_5697.FStar_Tactics_Types.entry_range)
              })
       | uu____5698 -> fail "flip: less than 2 goals")
  
let (later : Prims.unit tac) =
  bind get
    (fun ps  ->
       match ps.FStar_Tactics_Types.goals with
       | [] -> ret ()
       | g::gs ->
           set
             (let uu___108_5715 = ps  in
              {
                FStar_Tactics_Types.main_context =
                  (uu___108_5715.FStar_Tactics_Types.main_context);
                FStar_Tactics_Types.main_goal =
                  (uu___108_5715.FStar_Tactics_Types.main_goal);
                FStar_Tactics_Types.all_implicits =
                  (uu___108_5715.FStar_Tactics_Types.all_implicits);
                FStar_Tactics_Types.goals = (FStar_List.append gs [g]);
                FStar_Tactics_Types.smt_goals =
                  (uu___108_5715.FStar_Tactics_Types.smt_goals);
                FStar_Tactics_Types.depth =
                  (uu___108_5715.FStar_Tactics_Types.depth);
                FStar_Tactics_Types.__dump =
                  (uu___108_5715.FStar_Tactics_Types.__dump);
                FStar_Tactics_Types.psc =
                  (uu___108_5715.FStar_Tactics_Types.psc);
                FStar_Tactics_Types.entry_range =
                  (uu___108_5715.FStar_Tactics_Types.entry_range)
              }))
  
let (qed : Prims.unit tac) =
  bind get
    (fun ps  ->
       match ps.FStar_Tactics_Types.goals with
       | [] -> ret ()
       | uu____5724 -> fail "Not done!")
  
let (cases :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 tac)
  =
  fun t  ->
    let uu____5742 =
      bind cur_goal
        (fun g  ->
           let uu____5756 = __tc g.FStar_Tactics_Types.context t  in
           bind uu____5756
             (fun uu____5792  ->
                match uu____5792 with
                | (t1,typ,guard) ->
                    let uu____5808 = FStar_Syntax_Util.head_and_args typ  in
                    (match uu____5808 with
                     | (hd1,args) ->
                         let uu____5851 =
                           let uu____5864 =
                             let uu____5865 = FStar_Syntax_Util.un_uinst hd1
                                in
                             uu____5865.FStar_Syntax_Syntax.n  in
                           (uu____5864, args)  in
                         (match uu____5851 with
                          | (FStar_Syntax_Syntax.Tm_fvar
                             fv,(p,uu____5884)::(q,uu____5886)::[]) when
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
                                let uu___109_5924 = g  in
                                let uu____5925 =
                                  FStar_TypeChecker_Env.push_bv
                                    g.FStar_Tactics_Types.context v_p
                                   in
                                {
                                  FStar_Tactics_Types.context = uu____5925;
                                  FStar_Tactics_Types.witness =
                                    (uu___109_5924.FStar_Tactics_Types.witness);
                                  FStar_Tactics_Types.goal_ty =
                                    (uu___109_5924.FStar_Tactics_Types.goal_ty);
                                  FStar_Tactics_Types.opts =
                                    (uu___109_5924.FStar_Tactics_Types.opts);
                                  FStar_Tactics_Types.is_guard =
                                    (uu___109_5924.FStar_Tactics_Types.is_guard)
                                }  in
                              let g2 =
                                let uu___110_5927 = g  in
                                let uu____5928 =
                                  FStar_TypeChecker_Env.push_bv
                                    g.FStar_Tactics_Types.context v_q
                                   in
                                {
                                  FStar_Tactics_Types.context = uu____5928;
                                  FStar_Tactics_Types.witness =
                                    (uu___110_5927.FStar_Tactics_Types.witness);
                                  FStar_Tactics_Types.goal_ty =
                                    (uu___110_5927.FStar_Tactics_Types.goal_ty);
                                  FStar_Tactics_Types.opts =
                                    (uu___110_5927.FStar_Tactics_Types.opts);
                                  FStar_Tactics_Types.is_guard =
                                    (uu___110_5927.FStar_Tactics_Types.is_guard)
                                }  in
                              bind dismiss
                                (fun uu____5935  ->
                                   let uu____5936 = add_goals [g1; g2]  in
                                   bind uu____5936
                                     (fun uu____5945  ->
                                        let uu____5946 =
                                          let uu____5951 =
                                            FStar_Syntax_Syntax.bv_to_name
                                              v_p
                                             in
                                          let uu____5952 =
                                            FStar_Syntax_Syntax.bv_to_name
                                              v_q
                                             in
                                          (uu____5951, uu____5952)  in
                                        ret uu____5946))
                          | uu____5957 ->
                              let uu____5970 =
                                tts g.FStar_Tactics_Types.context typ  in
                              fail1 "Not a disjunction: %s" uu____5970))))
       in
    FStar_All.pipe_left (wrap_err "cases") uu____5742
  
let (set_options : Prims.string -> Prims.unit tac) =
  fun s  ->
    bind cur_goal
      (fun g  ->
         FStar_Options.push ();
         (let uu____6008 = FStar_Util.smap_copy g.FStar_Tactics_Types.opts
             in
          FStar_Options.set uu____6008);
         (let res = FStar_Options.set_options FStar_Options.Set s  in
          let opts' = FStar_Options.peek ()  in
          FStar_Options.pop ();
          (match res with
           | FStar_Getopt.Success  ->
               let g' =
                 let uu___111_6015 = g  in
                 {
                   FStar_Tactics_Types.context =
                     (uu___111_6015.FStar_Tactics_Types.context);
                   FStar_Tactics_Types.witness =
                     (uu___111_6015.FStar_Tactics_Types.witness);
                   FStar_Tactics_Types.goal_ty =
                     (uu___111_6015.FStar_Tactics_Types.goal_ty);
                   FStar_Tactics_Types.opts = opts';
                   FStar_Tactics_Types.is_guard =
                     (uu___111_6015.FStar_Tactics_Types.is_guard)
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
      let uu____6059 =
        bind cur_goal
          (fun goal  ->
             let env =
               FStar_TypeChecker_Env.set_expected_typ
                 goal.FStar_Tactics_Types.context ty
                in
             let uu____6067 = __tc env tm  in
             bind uu____6067
               (fun uu____6087  ->
                  match uu____6087 with
                  | (tm1,typ,guard) ->
                      (FStar_TypeChecker_Rel.force_trivial_guard env guard;
                       ret tm1)))
         in
      FStar_All.pipe_left (wrap_err "unquote") uu____6059
  
let (uvar_env :
  env ->
    FStar_Syntax_Syntax.typ FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.term tac)
  =
  fun env  ->
    fun ty  ->
      let uu____6118 =
        match ty with
        | FStar_Pervasives_Native.Some ty1 -> ret ty1
        | FStar_Pervasives_Native.None  ->
            let uu____6124 =
              let uu____6125 = FStar_Syntax_Util.type_u ()  in
              FStar_All.pipe_left FStar_Pervasives_Native.fst uu____6125  in
            new_uvar "uvar_env.2" env uu____6124
         in
      bind uu____6118
        (fun typ  ->
           let uu____6137 = new_uvar "uvar_env" env typ  in
           bind uu____6137 (fun t  -> ret t))
  
let (unshelve : FStar_Syntax_Syntax.term -> Prims.unit tac) =
  fun t  ->
    let uu____6149 =
      bind cur_goal
        (fun goal  ->
           let uu____6155 = __tc goal.FStar_Tactics_Types.context t  in
           bind uu____6155
             (fun uu____6175  ->
                match uu____6175 with
                | (t1,typ,guard) ->
                    let uu____6187 =
                      must_trivial goal.FStar_Tactics_Types.context guard  in
                    bind uu____6187
                      (fun uu____6192  ->
                         let uu____6193 =
                           let uu____6196 =
                             let uu___112_6197 = goal  in
                             let uu____6198 =
                               bnorm goal.FStar_Tactics_Types.context t1  in
                             let uu____6199 =
                               bnorm goal.FStar_Tactics_Types.context typ  in
                             {
                               FStar_Tactics_Types.context =
                                 (uu___112_6197.FStar_Tactics_Types.context);
                               FStar_Tactics_Types.witness = uu____6198;
                               FStar_Tactics_Types.goal_ty = uu____6199;
                               FStar_Tactics_Types.opts =
                                 (uu___112_6197.FStar_Tactics_Types.opts);
                               FStar_Tactics_Types.is_guard = false
                             }  in
                           [uu____6196]  in
                         add_goals uu____6193)))
       in
    FStar_All.pipe_left (wrap_err "unshelve") uu____6149
  
let (unify :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool tac) =
  fun t1  ->
    fun t2  ->
      bind get
        (fun ps  ->
           let uu____6217 =
             do_unify ps.FStar_Tactics_Types.main_context t1 t2  in
           ret uu____6217)
  
let (launch_process :
  Prims.string -> Prims.string -> Prims.string -> Prims.string tac) =
  fun prog  ->
    fun args  ->
      fun input  ->
        bind idtac
          (fun uu____6234  ->
             let uu____6235 = FStar_Options.unsafe_tactic_exec ()  in
             if uu____6235
             then
               let s =
                 FStar_Util.launch_process true "tactic_launch" prog args
                   input (fun uu____6241  -> fun uu____6242  -> false)
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
      let uu____6258 =
        FStar_TypeChecker_Util.new_implicit_var "proofstate_of_goal_ty"
          typ.FStar_Syntax_Syntax.pos env typ
         in
      match uu____6258 with
      | (u,uu____6276,g_u) ->
          let g =
            let uu____6291 = FStar_Options.peek ()  in
            {
              FStar_Tactics_Types.context = env;
              FStar_Tactics_Types.witness = u;
              FStar_Tactics_Types.goal_ty = typ;
              FStar_Tactics_Types.opts = uu____6291;
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
      let uu____6302 = goal_of_goal_ty env typ  in
      match uu____6302 with
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
  