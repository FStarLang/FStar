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
    let b = true  in
    let env = g.FStar_Tactics_Types.context  in
    let b1 =
      b && (FStar_TypeChecker_Env.closed env g.FStar_Tactics_Types.witness)
       in
    let b2 =
      b1 && (FStar_TypeChecker_Env.closed env g.FStar_Tactics_Types.goal_ty)
       in
    let rec aux b3 e =
      let uu____973 = FStar_TypeChecker_Env.pop_bv e  in
      match uu____973 with
      | FStar_Pervasives_Native.None  -> b3
      | FStar_Pervasives_Native.Some (bv,e1) ->
          let b4 =
            b3 &&
              (FStar_TypeChecker_Env.closed e1 bv.FStar_Syntax_Syntax.sort)
             in
          aux b4 e1
       in
    let uu____991 =
      (let uu____994 = aux b2 env  in Prims.op_Negation uu____994) &&
        (let uu____996 = FStar_ST.op_Bang nwarn  in
         uu____996 < (Prims.parse_int "5"))
       in
    if uu____991
    then
      ((let uu____1017 =
          let uu____1022 =
            let uu____1023 = goal_to_string g  in
            FStar_Util.format1
              "The following goal is ill-formed. Keeping calm and carrying on...\n<%s>\n\n"
              uu____1023
             in
          (FStar_Errors.Warning_IllFormedGoal, uu____1022)  in
        FStar_Errors.log_issue
          (g.FStar_Tactics_Types.goal_ty).FStar_Syntax_Syntax.pos uu____1017);
       (let uu____1024 =
          let uu____1025 = FStar_ST.op_Bang nwarn  in
          uu____1025 + (Prims.parse_int "1")  in
        FStar_ST.op_Colon_Equals nwarn uu____1024))
    else ()
  
let (add_goals : FStar_Tactics_Types.goal Prims.list -> Prims.unit tac) =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___63_1082 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___63_1082.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___63_1082.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___63_1082.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (FStar_List.append gs p.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___63_1082.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___63_1082.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___63_1082.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___63_1082.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___63_1082.FStar_Tactics_Types.entry_range)
            }))
  
let (add_smt_goals : FStar_Tactics_Types.goal Prims.list -> Prims.unit tac) =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___64_1100 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___64_1100.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___64_1100.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___64_1100.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___64_1100.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (FStar_List.append gs p.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___64_1100.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___64_1100.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___64_1100.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___64_1100.FStar_Tactics_Types.entry_range)
            }))
  
let (push_goals : FStar_Tactics_Types.goal Prims.list -> Prims.unit tac) =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___65_1118 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___65_1118.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___65_1118.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___65_1118.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (FStar_List.append p.FStar_Tactics_Types.goals gs);
              FStar_Tactics_Types.smt_goals =
                (uu___65_1118.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___65_1118.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___65_1118.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___65_1118.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___65_1118.FStar_Tactics_Types.entry_range)
            }))
  
let (push_smt_goals : FStar_Tactics_Types.goal Prims.list -> Prims.unit tac)
  =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___66_1136 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___66_1136.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___66_1136.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___66_1136.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___66_1136.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (FStar_List.append p.FStar_Tactics_Types.smt_goals gs);
              FStar_Tactics_Types.depth =
                (uu___66_1136.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___66_1136.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___66_1136.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___66_1136.FStar_Tactics_Types.entry_range)
            }))
  
let (replace_cur : FStar_Tactics_Types.goal -> Prims.unit tac) =
  fun g  -> bind dismiss (fun uu____1145  -> add_goals [g]) 
let (add_implicits : implicits -> Prims.unit tac) =
  fun i  ->
    bind get
      (fun p  ->
         set
           (let uu___67_1157 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___67_1157.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___67_1157.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (FStar_List.append i p.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___67_1157.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___67_1157.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___67_1157.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___67_1157.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___67_1157.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___67_1157.FStar_Tactics_Types.entry_range)
            }))
  
let (new_uvar :
  Prims.string ->
    env -> FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.term tac)
  =
  fun reason  ->
    fun env  ->
      fun typ  ->
        let uu____1183 =
          FStar_TypeChecker_Util.new_implicit_var reason
            typ.FStar_Syntax_Syntax.pos env typ
           in
        match uu____1183 with
        | (u,uu____1199,g_u) ->
            let uu____1213 =
              add_implicits g_u.FStar_TypeChecker_Env.implicits  in
            bind uu____1213 (fun uu____1217  -> ret u)
  
let (is_true : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____1221 = FStar_Syntax_Util.un_squash t  in
    match uu____1221 with
    | FStar_Pervasives_Native.Some t' ->
        let uu____1231 =
          let uu____1232 = FStar_Syntax_Subst.compress t'  in
          uu____1232.FStar_Syntax_Syntax.n  in
        (match uu____1231 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.true_lid
         | uu____1236 -> false)
    | uu____1237 -> false
  
let (is_false : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____1245 = FStar_Syntax_Util.un_squash t  in
    match uu____1245 with
    | FStar_Pervasives_Native.Some t' ->
        let uu____1255 =
          let uu____1256 = FStar_Syntax_Subst.compress t'  in
          uu____1256.FStar_Syntax_Syntax.n  in
        (match uu____1255 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.false_lid
         | uu____1260 -> false)
    | uu____1261 -> false
  
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
            let uu____1301 = env.FStar_TypeChecker_Env.universe_of env phi
               in
            FStar_Syntax_Util.mk_squash uu____1301 phi  in
          let uu____1302 = new_uvar reason env typ  in
          bind uu____1302
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
             let uu____1358 =
               (ps.FStar_Tactics_Types.main_context).FStar_TypeChecker_Env.type_of
                 e t
                in
             ret uu____1358
           with
           | ex ->
               let uu____1385 = tts e t  in
               let uu____1386 =
                 let uu____1387 = FStar_TypeChecker_Env.all_binders e  in
                 FStar_All.pipe_right uu____1387
                   (FStar_Syntax_Print.binders_to_string ", ")
                  in
               fail2 "Cannot type %s in context (%s)" uu____1385 uu____1386)
  
let (must_trivial : env -> FStar_TypeChecker_Env.guard_t -> Prims.unit tac) =
  fun e  ->
    fun g  ->
      try
        let uu____1411 =
          let uu____1412 =
            let uu____1413 = FStar_TypeChecker_Rel.discharge_guard_no_smt e g
               in
            FStar_All.pipe_left FStar_TypeChecker_Rel.is_trivial uu____1413
             in
          Prims.op_Negation uu____1412  in
        if uu____1411 then fail "got non-trivial guard" else ret ()
      with | uu____1422 -> fail "got non-trivial guard"
  
let (tc : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.typ tac) =
  fun t  ->
    let uu____1430 =
      bind cur_goal
        (fun goal  ->
           let uu____1436 = __tc goal.FStar_Tactics_Types.context t  in
           bind uu____1436
             (fun uu____1456  ->
                match uu____1456 with
                | (t1,typ,guard) ->
                    let uu____1468 =
                      must_trivial goal.FStar_Tactics_Types.context guard  in
                    bind uu____1468 (fun uu____1472  -> ret typ)))
       in
    FStar_All.pipe_left (wrap_err "tc") uu____1430
  
let (add_irrelevant_goal :
  Prims.string ->
    env ->
      FStar_Syntax_Syntax.typ -> FStar_Options.optionstate -> Prims.unit tac)
  =
  fun reason  ->
    fun env  ->
      fun phi  ->
        fun opts  ->
          let uu____1493 = mk_irrelevant_goal reason env phi opts  in
          bind uu____1493 (fun goal  -> add_goals [goal])
  
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
       let uu____1515 =
         istrivial goal.FStar_Tactics_Types.context
           goal.FStar_Tactics_Types.goal_ty
          in
       if uu____1515
       then solve goal FStar_Syntax_Util.exp_unit
       else
         (let uu____1519 =
            tts goal.FStar_Tactics_Types.context
              goal.FStar_Tactics_Types.goal_ty
             in
          fail1 "Not a trivial goal: %s" uu____1519))
  
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
          let uu____1536 =
            let uu____1537 = FStar_TypeChecker_Rel.simplify_guard e g  in
            uu____1537.FStar_TypeChecker_Env.guard_f  in
          match uu____1536 with
          | FStar_TypeChecker_Common.Trivial  -> ret ()
          | FStar_TypeChecker_Common.NonTrivial f ->
              let uu____1541 = istrivial e f  in
              if uu____1541
              then ret ()
              else
                (let uu____1545 = mk_irrelevant_goal reason e f opts  in
                 bind uu____1545
                   (fun goal  ->
                      let goal1 =
                        let uu___72_1552 = goal  in
                        {
                          FStar_Tactics_Types.context =
                            (uu___72_1552.FStar_Tactics_Types.context);
                          FStar_Tactics_Types.witness =
                            (uu___72_1552.FStar_Tactics_Types.witness);
                          FStar_Tactics_Types.goal_ty =
                            (uu___72_1552.FStar_Tactics_Types.goal_ty);
                          FStar_Tactics_Types.opts =
                            (uu___72_1552.FStar_Tactics_Types.opts);
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
          let uu____1573 =
            let uu____1574 = FStar_TypeChecker_Rel.simplify_guard e g  in
            uu____1574.FStar_TypeChecker_Env.guard_f  in
          match uu____1573 with
          | FStar_TypeChecker_Common.Trivial  ->
              ret FStar_Pervasives_Native.None
          | FStar_TypeChecker_Common.NonTrivial f ->
              let uu____1582 = istrivial e f  in
              if uu____1582
              then ret FStar_Pervasives_Native.None
              else
                (let uu____1590 = mk_irrelevant_goal reason e f opts  in
                 bind uu____1590
                   (fun goal  ->
                      ret
                        (FStar_Pervasives_Native.Some
                           (let uu___73_1600 = goal  in
                            {
                              FStar_Tactics_Types.context =
                                (uu___73_1600.FStar_Tactics_Types.context);
                              FStar_Tactics_Types.witness =
                                (uu___73_1600.FStar_Tactics_Types.witness);
                              FStar_Tactics_Types.goal_ty =
                                (uu___73_1600.FStar_Tactics_Types.goal_ty);
                              FStar_Tactics_Types.opts =
                                (uu___73_1600.FStar_Tactics_Types.opts);
                              FStar_Tactics_Types.is_guard = true
                            }))))
  
let (smt : Prims.unit tac) =
  bind cur_goal
    (fun g  ->
       let uu____1608 = is_irrelevant g  in
       if uu____1608
       then bind dismiss (fun uu____1612  -> add_smt_goals [g])
       else
         (let uu____1614 =
            tts g.FStar_Tactics_Types.context g.FStar_Tactics_Types.goal_ty
             in
          fail1 "goal is not irrelevant: cannot dispatch to smt (%s)"
            uu____1614))
  
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
             let uu____1655 =
               try
                 let uu____1689 =
                   let uu____1698 = FStar_BigInt.to_int_fs n1  in
                   FStar_List.splitAt uu____1698 p.FStar_Tactics_Types.goals
                    in
                 ret uu____1689
               with | uu____1720 -> fail "divide: not enough goals"  in
             bind uu____1655
               (fun uu____1747  ->
                  match uu____1747 with
                  | (lgs,rgs) ->
                      let lp =
                        let uu___74_1773 = p  in
                        {
                          FStar_Tactics_Types.main_context =
                            (uu___74_1773.FStar_Tactics_Types.main_context);
                          FStar_Tactics_Types.main_goal =
                            (uu___74_1773.FStar_Tactics_Types.main_goal);
                          FStar_Tactics_Types.all_implicits =
                            (uu___74_1773.FStar_Tactics_Types.all_implicits);
                          FStar_Tactics_Types.goals = lgs;
                          FStar_Tactics_Types.smt_goals = [];
                          FStar_Tactics_Types.depth =
                            (uu___74_1773.FStar_Tactics_Types.depth);
                          FStar_Tactics_Types.__dump =
                            (uu___74_1773.FStar_Tactics_Types.__dump);
                          FStar_Tactics_Types.psc =
                            (uu___74_1773.FStar_Tactics_Types.psc);
                          FStar_Tactics_Types.entry_range =
                            (uu___74_1773.FStar_Tactics_Types.entry_range)
                        }  in
                      let rp =
                        let uu___75_1775 = p  in
                        {
                          FStar_Tactics_Types.main_context =
                            (uu___75_1775.FStar_Tactics_Types.main_context);
                          FStar_Tactics_Types.main_goal =
                            (uu___75_1775.FStar_Tactics_Types.main_goal);
                          FStar_Tactics_Types.all_implicits =
                            (uu___75_1775.FStar_Tactics_Types.all_implicits);
                          FStar_Tactics_Types.goals = rgs;
                          FStar_Tactics_Types.smt_goals = [];
                          FStar_Tactics_Types.depth =
                            (uu___75_1775.FStar_Tactics_Types.depth);
                          FStar_Tactics_Types.__dump =
                            (uu___75_1775.FStar_Tactics_Types.__dump);
                          FStar_Tactics_Types.psc =
                            (uu___75_1775.FStar_Tactics_Types.psc);
                          FStar_Tactics_Types.entry_range =
                            (uu___75_1775.FStar_Tactics_Types.entry_range)
                        }  in
                      let uu____1776 = set lp  in
                      bind uu____1776
                        (fun uu____1784  ->
                           bind l
                             (fun a  ->
                                bind get
                                  (fun lp'  ->
                                     let uu____1798 = set rp  in
                                     bind uu____1798
                                       (fun uu____1806  ->
                                          bind r
                                            (fun b  ->
                                               bind get
                                                 (fun rp'  ->
                                                    let p' =
                                                      let uu___76_1822 = p
                                                         in
                                                      {
                                                        FStar_Tactics_Types.main_context
                                                          =
                                                          (uu___76_1822.FStar_Tactics_Types.main_context);
                                                        FStar_Tactics_Types.main_goal
                                                          =
                                                          (uu___76_1822.FStar_Tactics_Types.main_goal);
                                                        FStar_Tactics_Types.all_implicits
                                                          =
                                                          (uu___76_1822.FStar_Tactics_Types.all_implicits);
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
                                                          (uu___76_1822.FStar_Tactics_Types.depth);
                                                        FStar_Tactics_Types.__dump
                                                          =
                                                          (uu___76_1822.FStar_Tactics_Types.__dump);
                                                        FStar_Tactics_Types.psc
                                                          =
                                                          (uu___76_1822.FStar_Tactics_Types.psc);
                                                        FStar_Tactics_Types.entry_range
                                                          =
                                                          (uu___76_1822.FStar_Tactics_Types.entry_range)
                                                      }  in
                                                    let uu____1823 = set p'
                                                       in
                                                    bind uu____1823
                                                      (fun uu____1831  ->
                                                         ret (a, b))))))))))
  
let focus : 'a . 'a tac -> 'a tac =
  fun f  ->
    let uu____1849 = divide FStar_BigInt.one f idtac  in
    bind uu____1849
      (fun uu____1862  -> match uu____1862 with | (a,()) -> ret a)
  
let rec map : 'a . 'a tac -> 'a Prims.list tac =
  fun tau  ->
    bind get
      (fun p  ->
         match p.FStar_Tactics_Types.goals with
         | [] -> ret []
         | uu____1896::uu____1897 ->
             let uu____1900 =
               let uu____1909 = map tau  in
               divide FStar_BigInt.one tau uu____1909  in
             bind uu____1900
               (fun uu____1927  ->
                  match uu____1927 with | (h,t) -> ret (h :: t)))
  
let (seq : Prims.unit tac -> Prims.unit tac -> Prims.unit tac) =
  fun t1  ->
    fun t2  ->
      let uu____1964 =
        bind t1
          (fun uu____1969  ->
             let uu____1970 = map t2  in
             bind uu____1970 (fun uu____1978  -> ret ()))
         in
      focus uu____1964
  
let (intro : FStar_Syntax_Syntax.binder tac) =
  bind cur_goal
    (fun goal  ->
       let uu____1991 =
         FStar_Syntax_Util.arrow_one goal.FStar_Tactics_Types.goal_ty  in
       match uu____1991 with
       | FStar_Pervasives_Native.Some (b,c) ->
           let uu____2006 =
             let uu____2007 = FStar_Syntax_Util.is_total_comp c  in
             Prims.op_Negation uu____2007  in
           if uu____2006
           then fail "Codomain is effectful"
           else
             (let env' =
                FStar_TypeChecker_Env.push_binders
                  goal.FStar_Tactics_Types.context [b]
                 in
              let typ' = comp_to_typ c  in
              let uu____2013 = new_uvar "intro" env' typ'  in
              bind uu____2013
                (fun u  ->
                   let uu____2020 =
                     let uu____2021 =
                       FStar_Syntax_Util.abs [b] u
                         FStar_Pervasives_Native.None
                        in
                     trysolve goal uu____2021  in
                   if uu____2020
                   then
                     let uu____2024 =
                       let uu____2027 =
                         let uu___79_2028 = goal  in
                         let uu____2029 = bnorm env' u  in
                         let uu____2030 = bnorm env' typ'  in
                         {
                           FStar_Tactics_Types.context = env';
                           FStar_Tactics_Types.witness = uu____2029;
                           FStar_Tactics_Types.goal_ty = uu____2030;
                           FStar_Tactics_Types.opts =
                             (uu___79_2028.FStar_Tactics_Types.opts);
                           FStar_Tactics_Types.is_guard =
                             (uu___79_2028.FStar_Tactics_Types.is_guard)
                         }  in
                       replace_cur uu____2027  in
                     bind uu____2024 (fun uu____2032  -> ret b)
                   else fail "intro: unification failed"))
       | FStar_Pervasives_Native.None  ->
           let uu____2038 =
             tts goal.FStar_Tactics_Types.context
               goal.FStar_Tactics_Types.goal_ty
              in
           fail1 "intro: goal is not an arrow (%s)" uu____2038)
  
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
       (let uu____2065 =
          FStar_Syntax_Util.arrow_one goal.FStar_Tactics_Types.goal_ty  in
        match uu____2065 with
        | FStar_Pervasives_Native.Some (b,c) ->
            let uu____2084 =
              let uu____2085 = FStar_Syntax_Util.is_total_comp c  in
              Prims.op_Negation uu____2085  in
            if uu____2084
            then fail "Codomain is effectful"
            else
              (let bv =
                 FStar_Syntax_Syntax.gen_bv "__recf"
                   FStar_Pervasives_Native.None
                   goal.FStar_Tactics_Types.goal_ty
                  in
               let bs =
                 let uu____2101 = FStar_Syntax_Syntax.mk_binder bv  in
                 [uu____2101; b]  in
               let env' =
                 FStar_TypeChecker_Env.push_binders
                   goal.FStar_Tactics_Types.context bs
                  in
               let uu____2103 =
                 let uu____2106 = comp_to_typ c  in
                 new_uvar "intro_rec" env' uu____2106  in
               bind uu____2103
                 (fun u  ->
                    let lb =
                      let uu____2122 =
                        FStar_Syntax_Util.abs [b] u
                          FStar_Pervasives_Native.None
                         in
                      FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl bv) []
                        goal.FStar_Tactics_Types.goal_ty
                        FStar_Parser_Const.effect_Tot_lid uu____2122 []
                       in
                    let body = FStar_Syntax_Syntax.bv_to_name bv  in
                    let uu____2128 =
                      FStar_Syntax_Subst.close_let_rec [lb] body  in
                    match uu____2128 with
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
                          let uu____2165 =
                            let uu____2168 =
                              let uu___80_2169 = goal  in
                              let uu____2170 = bnorm env' u  in
                              let uu____2171 =
                                let uu____2172 = comp_to_typ c  in
                                bnorm env' uu____2172  in
                              {
                                FStar_Tactics_Types.context = env';
                                FStar_Tactics_Types.witness = uu____2170;
                                FStar_Tactics_Types.goal_ty = uu____2171;
                                FStar_Tactics_Types.opts =
                                  (uu___80_2169.FStar_Tactics_Types.opts);
                                FStar_Tactics_Types.is_guard =
                                  (uu___80_2169.FStar_Tactics_Types.is_guard)
                              }  in
                            replace_cur uu____2168  in
                          bind uu____2165
                            (fun uu____2179  ->
                               let uu____2180 =
                                 let uu____2185 =
                                   FStar_Syntax_Syntax.mk_binder bv  in
                                 (uu____2185, b)  in
                               ret uu____2180)
                        else fail "intro_rec: unification failed"))
        | FStar_Pervasives_Native.None  ->
            let uu____2199 =
              tts goal.FStar_Tactics_Types.context
                goal.FStar_Tactics_Types.goal_ty
               in
            fail1 "intro_rec: goal is not an arrow (%s)" uu____2199))
  
let (norm : FStar_Syntax_Embeddings.norm_step Prims.list -> Prims.unit tac) =
  fun s  ->
    bind cur_goal
      (fun goal  ->
         mlog
           (fun uu____2219  ->
              let uu____2220 =
                FStar_Syntax_Print.term_to_string
                  goal.FStar_Tactics_Types.witness
                 in
              FStar_Util.print1 "norm: witness = %s\n" uu____2220)
           (fun uu____2225  ->
              let steps =
                let uu____2229 = FStar_TypeChecker_Normalize.tr_norm_steps s
                   in
                FStar_List.append
                  [FStar_TypeChecker_Normalize.Reify;
                  FStar_TypeChecker_Normalize.UnfoldTac] uu____2229
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
                (let uu___81_2236 = goal  in
                 {
                   FStar_Tactics_Types.context =
                     (uu___81_2236.FStar_Tactics_Types.context);
                   FStar_Tactics_Types.witness = w;
                   FStar_Tactics_Types.goal_ty = t;
                   FStar_Tactics_Types.opts =
                     (uu___81_2236.FStar_Tactics_Types.opts);
                   FStar_Tactics_Types.is_guard =
                     (uu___81_2236.FStar_Tactics_Types.is_guard)
                 })))
  
let (norm_term_env :
  env ->
    FStar_Syntax_Embeddings.norm_step Prims.list ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac)
  =
  fun e  ->
    fun s  ->
      fun t  ->
        let uu____2254 =
          mlog
            (fun uu____2259  ->
               let uu____2260 = FStar_Syntax_Print.term_to_string t  in
               FStar_Util.print1 "norm_term: tm = %s\n" uu____2260)
            (fun uu____2262  ->
               bind get
                 (fun ps  ->
                    let uu____2266 = __tc e t  in
                    bind uu____2266
                      (fun uu____2288  ->
                         match uu____2288 with
                         | (t1,uu____2298,guard) ->
                             (FStar_TypeChecker_Rel.force_trivial_guard e
                                guard;
                              (let steps =
                                 let uu____2304 =
                                   FStar_TypeChecker_Normalize.tr_norm_steps
                                     s
                                    in
                                 FStar_List.append
                                   [FStar_TypeChecker_Normalize.Reify;
                                   FStar_TypeChecker_Normalize.UnfoldTac]
                                   uu____2304
                                  in
                               let t2 =
                                 normalize steps
                                   ps.FStar_Tactics_Types.main_context t1
                                  in
                               ret t2)))))
           in
        FStar_All.pipe_left (wrap_err "norm_term") uu____2254
  
let (refine_intro : Prims.unit tac) =
  let uu____2316 =
    bind cur_goal
      (fun g  ->
         let uu____2323 =
           FStar_TypeChecker_Rel.base_and_refinement
             g.FStar_Tactics_Types.context g.FStar_Tactics_Types.goal_ty
            in
         match uu____2323 with
         | (uu____2336,FStar_Pervasives_Native.None ) ->
             fail "not a refinement"
         | (t,FStar_Pervasives_Native.Some (bv,phi)) ->
             let g1 =
               let uu___82_2361 = g  in
               {
                 FStar_Tactics_Types.context =
                   (uu___82_2361.FStar_Tactics_Types.context);
                 FStar_Tactics_Types.witness =
                   (uu___82_2361.FStar_Tactics_Types.witness);
                 FStar_Tactics_Types.goal_ty = t;
                 FStar_Tactics_Types.opts =
                   (uu___82_2361.FStar_Tactics_Types.opts);
                 FStar_Tactics_Types.is_guard =
                   (uu___82_2361.FStar_Tactics_Types.is_guard)
               }  in
             let uu____2362 =
               let uu____2367 =
                 let uu____2372 =
                   let uu____2373 = FStar_Syntax_Syntax.mk_binder bv  in
                   [uu____2373]  in
                 FStar_Syntax_Subst.open_term uu____2372 phi  in
               match uu____2367 with
               | (bvs,phi1) ->
                   let uu____2380 =
                     let uu____2381 = FStar_List.hd bvs  in
                     FStar_Pervasives_Native.fst uu____2381  in
                   (uu____2380, phi1)
                in
             (match uu____2362 with
              | (bv1,phi1) ->
                  let uu____2394 =
                    let uu____2397 =
                      FStar_Syntax_Subst.subst
                        [FStar_Syntax_Syntax.NT
                           (bv1, (g.FStar_Tactics_Types.witness))] phi1
                       in
                    mk_irrelevant_goal "refine_intro refinement"
                      g.FStar_Tactics_Types.context uu____2397
                      g.FStar_Tactics_Types.opts
                     in
                  bind uu____2394
                    (fun g2  ->
                       bind dismiss (fun uu____2401  -> add_goals [g1; g2]))))
     in
  FStar_All.pipe_left (wrap_err "refine_intro") uu____2316 
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
             let uu____2425 = __tc env t  in
             bind uu____2425
               (fun uu____2445  ->
                  match uu____2445 with
                  | (t1,typ,guard) ->
                      let uu____2457 =
                        if force_guard
                        then
                          must_trivial goal.FStar_Tactics_Types.context guard
                        else
                          add_goal_from_guard "__exact typing"
                            goal.FStar_Tactics_Types.context guard
                            goal.FStar_Tactics_Types.opts
                         in
                      bind uu____2457
                        (fun uu____2464  ->
                           mlog
                             (fun uu____2468  ->
                                let uu____2469 =
                                  tts goal.FStar_Tactics_Types.context typ
                                   in
                                let uu____2470 =
                                  tts goal.FStar_Tactics_Types.context
                                    goal.FStar_Tactics_Types.goal_ty
                                   in
                                FStar_Util.print2
                                  "exact: unifying %s and %s\n" uu____2469
                                  uu____2470)
                             (fun uu____2473  ->
                                let uu____2474 =
                                  do_unify goal.FStar_Tactics_Types.context
                                    typ goal.FStar_Tactics_Types.goal_ty
                                   in
                                if uu____2474
                                then solve goal t1
                                else
                                  (let uu____2478 =
                                     tts goal.FStar_Tactics_Types.context t1
                                      in
                                   let uu____2479 =
                                     tts goal.FStar_Tactics_Types.context typ
                                      in
                                   let uu____2480 =
                                     tts goal.FStar_Tactics_Types.context
                                       goal.FStar_Tactics_Types.goal_ty
                                      in
                                   let uu____2481 =
                                     tts goal.FStar_Tactics_Types.context
                                       goal.FStar_Tactics_Types.witness
                                      in
                                   fail4
                                     "%s : %s does not exactly solve the goal %s (witness = %s)"
                                     uu____2478 uu____2479 uu____2480
                                     uu____2481)))))
  
let (t_exact :
  Prims.bool -> Prims.bool -> FStar_Syntax_Syntax.term -> Prims.unit tac) =
  fun set_expected_typ1  ->
    fun force_guard  ->
      fun tm  ->
        let uu____2495 =
          mlog
            (fun uu____2500  ->
               let uu____2501 = FStar_Syntax_Print.term_to_string tm  in
               FStar_Util.print1 "t_exact: tm = %s\n" uu____2501)
            (fun uu____2504  ->
               let uu____2505 =
                 let uu____2512 =
                   __exact_now set_expected_typ1 force_guard tm  in
                 trytac' uu____2512  in
               bind uu____2505
                 (fun uu___56_2521  ->
                    match uu___56_2521 with
                    | FStar_Util.Inr r -> ret ()
                    | FStar_Util.Inl e ->
                        let uu____2530 =
                          let uu____2537 =
                            let uu____2540 =
                              norm [FStar_Syntax_Embeddings.Delta]  in
                            bind uu____2540
                              (fun uu____2544  ->
                                 bind refine_intro
                                   (fun uu____2546  ->
                                      __exact_now set_expected_typ1
                                        force_guard tm))
                             in
                          trytac' uu____2537  in
                        bind uu____2530
                          (fun uu___55_2553  ->
                             match uu___55_2553 with
                             | FStar_Util.Inr r -> ret ()
                             | FStar_Util.Inl uu____2561 -> fail e)))
           in
        FStar_All.pipe_left (wrap_err "exact") uu____2495
  
let (uvar_free_in_goal :
  FStar_Syntax_Syntax.uvar -> FStar_Tactics_Types.goal -> Prims.bool) =
  fun u  ->
    fun g  ->
      if g.FStar_Tactics_Types.is_guard
      then false
      else
        (let free_uvars =
           let uu____2576 =
             let uu____2583 =
               FStar_Syntax_Free.uvars g.FStar_Tactics_Types.goal_ty  in
             FStar_Util.set_elements uu____2583  in
           FStar_List.map FStar_Pervasives_Native.fst uu____2576  in
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
          let uu____2643 = f x  in
          bind uu____2643
            (fun y  ->
               let uu____2651 = mapM f xs  in
               bind uu____2651 (fun ys  -> ret (y :: ys)))
  
exception NoUnif 
let (uu___is_NoUnif : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with | NoUnif  -> true | uu____2669 -> false
  
let rec (__apply :
  Prims.bool ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.typ -> Prims.unit tac)
  =
  fun uopt  ->
    fun tm  ->
      fun typ  ->
        bind cur_goal
          (fun goal  ->
             let uu____2686 =
               let uu____2691 = t_exact false true tm  in trytac uu____2691
                in
             bind uu____2686
               (fun uu___57_2698  ->
                  match uu___57_2698 with
                  | FStar_Pervasives_Native.Some r -> ret ()
                  | FStar_Pervasives_Native.None  ->
                      let uu____2704 = FStar_Syntax_Util.arrow_one typ  in
                      (match uu____2704 with
                       | FStar_Pervasives_Native.None  ->
                           FStar_Exn.raise NoUnif
                       | FStar_Pervasives_Native.Some ((bv,aq),c) ->
                           mlog
                             (fun uu____2736  ->
                                let uu____2737 =
                                  FStar_Syntax_Print.binder_to_string
                                    (bv, aq)
                                   in
                                FStar_Util.print1
                                  "__apply: pushing binder %s\n" uu____2737)
                             (fun uu____2740  ->
                                let uu____2741 =
                                  let uu____2742 =
                                    FStar_Syntax_Util.is_total_comp c  in
                                  Prims.op_Negation uu____2742  in
                                if uu____2741
                                then fail "apply: not total codomain"
                                else
                                  (let uu____2746 =
                                     new_uvar "apply"
                                       goal.FStar_Tactics_Types.context
                                       bv.FStar_Syntax_Syntax.sort
                                      in
                                   bind uu____2746
                                     (fun u  ->
                                        let tm' =
                                          FStar_Syntax_Syntax.mk_Tm_app tm
                                            [(u, aq)]
                                            FStar_Pervasives_Native.None
                                            (goal.FStar_Tactics_Types.context).FStar_TypeChecker_Env.range
                                           in
                                        let typ' =
                                          let uu____2766 = comp_to_typ c  in
                                          FStar_All.pipe_left
                                            (FStar_Syntax_Subst.subst
                                               [FStar_Syntax_Syntax.NT
                                                  (bv, u)]) uu____2766
                                           in
                                        let uu____2767 =
                                          __apply uopt tm' typ'  in
                                        bind uu____2767
                                          (fun uu____2775  ->
                                             let u1 =
                                               bnorm
                                                 goal.FStar_Tactics_Types.context
                                                 u
                                                in
                                             let uu____2777 =
                                               let uu____2778 =
                                                 let uu____2781 =
                                                   let uu____2782 =
                                                     FStar_Syntax_Util.head_and_args
                                                       u1
                                                      in
                                                   FStar_Pervasives_Native.fst
                                                     uu____2782
                                                    in
                                                 FStar_Syntax_Subst.compress
                                                   uu____2781
                                                  in
                                               uu____2778.FStar_Syntax_Syntax.n
                                                in
                                             match uu____2777 with
                                             | FStar_Syntax_Syntax.Tm_uvar
                                                 (uvar,uu____2810) ->
                                                 bind get
                                                   (fun ps  ->
                                                      let uu____2838 =
                                                        uopt &&
                                                          (uvar_free uvar ps)
                                                         in
                                                      if uu____2838
                                                      then ret ()
                                                      else
                                                        (let uu____2842 =
                                                           let uu____2845 =
                                                             let uu___83_2846
                                                               = goal  in
                                                             let uu____2847 =
                                                               bnorm
                                                                 goal.FStar_Tactics_Types.context
                                                                 u1
                                                                in
                                                             let uu____2848 =
                                                               bnorm
                                                                 goal.FStar_Tactics_Types.context
                                                                 bv.FStar_Syntax_Syntax.sort
                                                                in
                                                             {
                                                               FStar_Tactics_Types.context
                                                                 =
                                                                 (uu___83_2846.FStar_Tactics_Types.context);
                                                               FStar_Tactics_Types.witness
                                                                 = uu____2847;
                                                               FStar_Tactics_Types.goal_ty
                                                                 = uu____2848;
                                                               FStar_Tactics_Types.opts
                                                                 =
                                                                 (uu___83_2846.FStar_Tactics_Types.opts);
                                                               FStar_Tactics_Types.is_guard
                                                                 = false
                                                             }  in
                                                           [uu____2845]  in
                                                         add_goals uu____2842))
                                             | t -> ret ())))))))
  
let try_unif : 'a . 'a tac -> 'a tac -> 'a tac =
  fun t  ->
    fun t'  -> mk_tac (fun ps  -> try run t ps with | NoUnif  -> run t' ps)
  
let (apply : Prims.bool -> FStar_Syntax_Syntax.term -> Prims.unit tac) =
  fun uopt  ->
    fun tm  ->
      let uu____2894 =
        mlog
          (fun uu____2899  ->
             let uu____2900 = FStar_Syntax_Print.term_to_string tm  in
             FStar_Util.print1 "apply: tm = %s\n" uu____2900)
          (fun uu____2902  ->
             bind cur_goal
               (fun goal  ->
                  let uu____2906 = __tc goal.FStar_Tactics_Types.context tm
                     in
                  bind uu____2906
                    (fun uu____2927  ->
                       match uu____2927 with
                       | (tm1,typ,guard) ->
                           let uu____2939 =
                             let uu____2942 =
                               let uu____2945 = __apply uopt tm1 typ  in
                               bind uu____2945
                                 (fun uu____2949  ->
                                    add_goal_from_guard "apply guard"
                                      goal.FStar_Tactics_Types.context guard
                                      goal.FStar_Tactics_Types.opts)
                                in
                             focus uu____2942  in
                           let uu____2950 =
                             let uu____2953 =
                               tts goal.FStar_Tactics_Types.context tm1  in
                             let uu____2954 =
                               tts goal.FStar_Tactics_Types.context typ  in
                             let uu____2955 =
                               tts goal.FStar_Tactics_Types.context
                                 goal.FStar_Tactics_Types.goal_ty
                                in
                             fail3
                               "Cannot instantiate %s (of type %s) to match goal (%s)"
                               uu____2953 uu____2954 uu____2955
                              in
                           try_unif uu____2939 uu____2950)))
         in
      FStar_All.pipe_left (wrap_err "apply") uu____2894
  
let (apply_lemma : FStar_Syntax_Syntax.term -> Prims.unit tac) =
  fun tm  ->
    let uu____2967 =
      let uu____2970 =
        mlog
          (fun uu____2975  ->
             let uu____2976 = FStar_Syntax_Print.term_to_string tm  in
             FStar_Util.print1 "apply_lemma: tm = %s\n" uu____2976)
          (fun uu____2979  ->
             let is_unit_t t =
               let uu____2984 =
                 let uu____2985 = FStar_Syntax_Subst.compress t  in
                 uu____2985.FStar_Syntax_Syntax.n  in
               match uu____2984 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.unit_lid
                   -> true
               | uu____2989 -> false  in
             bind cur_goal
               (fun goal  ->
                  let uu____2993 = __tc goal.FStar_Tactics_Types.context tm
                     in
                  bind uu____2993
                    (fun uu____3015  ->
                       match uu____3015 with
                       | (tm1,t,guard) ->
                           let uu____3027 =
                             FStar_Syntax_Util.arrow_formals_comp t  in
                           (match uu____3027 with
                            | (bs,comp) ->
                                if
                                  Prims.op_Negation
                                    (FStar_Syntax_Util.is_lemma_comp comp)
                                then fail "not a lemma"
                                else
                                  (let uu____3057 =
                                     FStar_List.fold_left
                                       (fun uu____3103  ->
                                          fun uu____3104  ->
                                            match (uu____3103, uu____3104)
                                            with
                                            | ((uvs,guard1,subst1),(b,aq)) ->
                                                let b_t =
                                                  FStar_Syntax_Subst.subst
                                                    subst1
                                                    b.FStar_Syntax_Syntax.sort
                                                   in
                                                let uu____3207 =
                                                  is_unit_t b_t  in
                                                if uu____3207
                                                then
                                                  (((FStar_Syntax_Util.exp_unit,
                                                      aq) :: uvs), guard1,
                                                    ((FStar_Syntax_Syntax.NT
                                                        (b,
                                                          FStar_Syntax_Util.exp_unit))
                                                    :: subst1))
                                                else
                                                  (let uu____3245 =
                                                     FStar_TypeChecker_Util.new_implicit_var
                                                       "apply_lemma"
                                                       (goal.FStar_Tactics_Types.goal_ty).FStar_Syntax_Syntax.pos
                                                       goal.FStar_Tactics_Types.context
                                                       b_t
                                                      in
                                                   match uu____3245 with
                                                   | (u,uu____3275,g_u) ->
                                                       let uu____3289 =
                                                         FStar_TypeChecker_Rel.conj_guard
                                                           guard1 g_u
                                                          in
                                                       (((u, aq) :: uvs),
                                                         uu____3289,
                                                         ((FStar_Syntax_Syntax.NT
                                                             (b, u)) ::
                                                         subst1))))
                                       ([], guard, []) bs
                                      in
                                   match uu____3057 with
                                   | (uvs,implicits,subst1) ->
                                       let uvs1 = FStar_List.rev uvs  in
                                       let comp1 =
                                         FStar_Syntax_Subst.subst_comp subst1
                                           comp
                                          in
                                       let uu____3359 =
                                         let uu____3368 =
                                           let uu____3377 =
                                             FStar_Syntax_Util.comp_to_comp_typ
                                               comp1
                                              in
                                           uu____3377.FStar_Syntax_Syntax.effect_args
                                            in
                                         match uu____3368 with
                                         | pre::post::uu____3388 ->
                                             ((FStar_Pervasives_Native.fst
                                                 pre),
                                               (FStar_Pervasives_Native.fst
                                                  post))
                                         | uu____3429 ->
                                             failwith
                                               "apply_lemma: impossible: not a lemma"
                                          in
                                       (match uu____3359 with
                                        | (pre,post) ->
                                            let post1 =
                                              let uu____3461 =
                                                let uu____3470 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    FStar_Syntax_Util.exp_unit
                                                   in
                                                [uu____3470]  in
                                              FStar_Syntax_Util.mk_app post
                                                uu____3461
                                               in
                                            let uu____3471 =
                                              let uu____3472 =
                                                let uu____3473 =
                                                  FStar_Syntax_Util.mk_squash
                                                    FStar_Syntax_Syntax.U_zero
                                                    post1
                                                   in
                                                do_unify
                                                  goal.FStar_Tactics_Types.context
                                                  uu____3473
                                                  goal.FStar_Tactics_Types.goal_ty
                                                 in
                                              Prims.op_Negation uu____3472
                                               in
                                            if uu____3471
                                            then
                                              let uu____3476 =
                                                tts
                                                  goal.FStar_Tactics_Types.context
                                                  tm1
                                                 in
                                              let uu____3477 =
                                                let uu____3478 =
                                                  FStar_Syntax_Util.mk_squash
                                                    FStar_Syntax_Syntax.U_zero
                                                    post1
                                                   in
                                                tts
                                                  goal.FStar_Tactics_Types.context
                                                  uu____3478
                                                 in
                                              let uu____3479 =
                                                tts
                                                  goal.FStar_Tactics_Types.context
                                                  goal.FStar_Tactics_Types.goal_ty
                                                 in
                                              fail3
                                                "Cannot instantiate lemma %s (with postcondition: %s) to match goal (%s)"
                                                uu____3476 uu____3477
                                                uu____3479
                                            else
                                              (let uu____3481 =
                                                 add_implicits
                                                   implicits.FStar_TypeChecker_Env.implicits
                                                  in
                                               bind uu____3481
                                                 (fun uu____3486  ->
                                                    let uu____3487 =
                                                      solve goal
                                                        FStar_Syntax_Util.exp_unit
                                                       in
                                                    bind uu____3487
                                                      (fun uu____3495  ->
                                                         let is_free_uvar uv
                                                           t1 =
                                                           let free_uvars =
                                                             let uu____3506 =
                                                               let uu____3513
                                                                 =
                                                                 FStar_Syntax_Free.uvars
                                                                   t1
                                                                  in
                                                               FStar_Util.set_elements
                                                                 uu____3513
                                                                in
                                                             FStar_List.map
                                                               FStar_Pervasives_Native.fst
                                                               uu____3506
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
                                                           let uu____3554 =
                                                             FStar_Syntax_Util.head_and_args
                                                               t1
                                                              in
                                                           match uu____3554
                                                           with
                                                           | (hd1,uu____3570)
                                                               ->
                                                               (match 
                                                                  hd1.FStar_Syntax_Syntax.n
                                                                with
                                                                | FStar_Syntax_Syntax.Tm_uvar
                                                                    (uv,uu____3592)
                                                                    ->
                                                                    appears
                                                                    uv goals
                                                                | uu____3617
                                                                    -> false)
                                                            in
                                                         let uu____3618 =
                                                           FStar_All.pipe_right
                                                             implicits.FStar_TypeChecker_Env.implicits
                                                             (mapM
                                                                (fun
                                                                   uu____3690
                                                                    ->
                                                                   match uu____3690
                                                                   with
                                                                   | 
                                                                   (_msg,env,_uvar,term,typ,uu____3718)
                                                                    ->
                                                                    let uu____3719
                                                                    =
                                                                    FStar_Syntax_Util.head_and_args
                                                                    term  in
                                                                    (match uu____3719
                                                                    with
                                                                    | 
                                                                    (hd1,uu____3745)
                                                                    ->
                                                                    let uu____3766
                                                                    =
                                                                    let uu____3767
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    hd1  in
                                                                    uu____3767.FStar_Syntax_Syntax.n
                                                                     in
                                                                    (match uu____3766
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Tm_uvar
                                                                    uu____3780
                                                                    ->
                                                                    let uu____3797
                                                                    =
                                                                    let uu____3806
                                                                    =
                                                                    let uu____3809
                                                                    =
                                                                    let uu___86_3810
                                                                    = goal
                                                                     in
                                                                    let uu____3811
                                                                    =
                                                                    bnorm
                                                                    goal.FStar_Tactics_Types.context
                                                                    term  in
                                                                    let uu____3812
                                                                    =
                                                                    bnorm
                                                                    goal.FStar_Tactics_Types.context
                                                                    typ  in
                                                                    {
                                                                    FStar_Tactics_Types.context
                                                                    =
                                                                    (uu___86_3810.FStar_Tactics_Types.context);
                                                                    FStar_Tactics_Types.witness
                                                                    =
                                                                    uu____3811;
                                                                    FStar_Tactics_Types.goal_ty
                                                                    =
                                                                    uu____3812;
                                                                    FStar_Tactics_Types.opts
                                                                    =
                                                                    (uu___86_3810.FStar_Tactics_Types.opts);
                                                                    FStar_Tactics_Types.is_guard
                                                                    =
                                                                    (uu___86_3810.FStar_Tactics_Types.is_guard)
                                                                    }  in
                                                                    [uu____3809]
                                                                     in
                                                                    (uu____3806,
                                                                    [])  in
                                                                    ret
                                                                    uu____3797
                                                                    | 
                                                                    uu____3825
                                                                    ->
                                                                    let g_typ
                                                                    =
                                                                    let uu____3827
                                                                    =
                                                                    FStar_Options.__temp_fast_implicits
                                                                    ()  in
                                                                    if
                                                                    uu____3827
                                                                    then
                                                                    FStar_TypeChecker_TcTerm.check_type_of_well_typed_term
                                                                    false env
                                                                    term typ
                                                                    else
                                                                    (let term1
                                                                    =
                                                                    bnorm env
                                                                    term  in
                                                                    let uu____3830
                                                                    =
                                                                    let uu____3837
                                                                    =
                                                                    FStar_TypeChecker_Env.set_expected_typ
                                                                    env typ
                                                                     in
                                                                    env.FStar_TypeChecker_Env.type_of
                                                                    uu____3837
                                                                    term1  in
                                                                    match uu____3830
                                                                    with
                                                                    | 
                                                                    (uu____3838,uu____3839,g_typ)
                                                                    -> g_typ)
                                                                     in
                                                                    let uu____3841
                                                                    =
                                                                    goal_from_guard
                                                                    "apply_lemma solved arg"
                                                                    goal.FStar_Tactics_Types.context
                                                                    g_typ
                                                                    goal.FStar_Tactics_Types.opts
                                                                     in
                                                                    bind
                                                                    uu____3841
                                                                    (fun
                                                                    uu___58_3857
                                                                     ->
                                                                    match uu___58_3857
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
                                                         bind uu____3618
                                                           (fun goals_  ->
                                                              let sub_goals =
                                                                let uu____3925
                                                                  =
                                                                  FStar_List.map
                                                                    FStar_Pervasives_Native.fst
                                                                    goals_
                                                                   in
                                                                FStar_List.flatten
                                                                  uu____3925
                                                                 in
                                                              let smt_goals =
                                                                let uu____3947
                                                                  =
                                                                  FStar_List.map
                                                                    FStar_Pervasives_Native.snd
                                                                    goals_
                                                                   in
                                                                FStar_List.flatten
                                                                  uu____3947
                                                                 in
                                                              let rec filter'
                                                                a f xs =
                                                                match xs with
                                                                | [] -> []
                                                                | x::xs1 ->
                                                                    let uu____4002
                                                                    = f x xs1
                                                                     in
                                                                    if
                                                                    uu____4002
                                                                    then
                                                                    let uu____4005
                                                                    =
                                                                    filter'
                                                                    () f xs1
                                                                     in x ::
                                                                    uu____4005
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
                                                                    let uu____4019
                                                                    =
                                                                    checkone
                                                                    g.FStar_Tactics_Types.witness
                                                                    goals  in
                                                                    Prims.op_Negation
                                                                    uu____4019))
                                                                    a434 a435)
                                                                    (Obj.magic
                                                                    sub_goals))
                                                                 in
                                                              let uu____4020
                                                                =
                                                                add_goal_from_guard
                                                                  "apply_lemma guard"
                                                                  goal.FStar_Tactics_Types.context
                                                                  guard
                                                                  goal.FStar_Tactics_Types.opts
                                                                 in
                                                              bind uu____4020
                                                                (fun
                                                                   uu____4025
                                                                    ->
                                                                   let uu____4026
                                                                    =
                                                                    let uu____4029
                                                                    =
                                                                    let uu____4030
                                                                    =
                                                                    let uu____4031
                                                                    =
                                                                    FStar_Syntax_Util.mk_squash
                                                                    FStar_Syntax_Syntax.U_zero
                                                                    pre  in
                                                                    istrivial
                                                                    goal.FStar_Tactics_Types.context
                                                                    uu____4031
                                                                     in
                                                                    Prims.op_Negation
                                                                    uu____4030
                                                                     in
                                                                    if
                                                                    uu____4029
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
                                                                    uu____4026
                                                                    (fun
                                                                    uu____4037
                                                                     ->
                                                                    let uu____4038
                                                                    =
                                                                    add_smt_goals
                                                                    smt_goals
                                                                     in
                                                                    bind
                                                                    uu____4038
                                                                    (fun
                                                                    uu____4042
                                                                     ->
                                                                    add_goals
                                                                    sub_goals1)))))))))))))
         in
      focus uu____2970  in
    FStar_All.pipe_left (wrap_err "apply_lemma") uu____2967
  
let (destruct_eq' :
  FStar_Syntax_Syntax.typ ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun typ  ->
    let uu____4062 = FStar_Syntax_Util.destruct_typ_as_formula typ  in
    match uu____4062 with
    | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn
        (l,uu____4072::(e1,uu____4074)::(e2,uu____4076)::[])) when
        FStar_Ident.lid_equals l FStar_Parser_Const.eq2_lid ->
        FStar_Pervasives_Native.Some (e1, e2)
    | uu____4135 -> FStar_Pervasives_Native.None
  
let (destruct_eq :
  FStar_Syntax_Syntax.typ ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun typ  ->
    let uu____4157 = destruct_eq' typ  in
    match uu____4157 with
    | FStar_Pervasives_Native.Some t -> FStar_Pervasives_Native.Some t
    | FStar_Pervasives_Native.None  ->
        let uu____4187 = FStar_Syntax_Util.un_squash typ  in
        (match uu____4187 with
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
        let uu____4243 = FStar_TypeChecker_Env.pop_bv e1  in
        match uu____4243 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (bv',e') ->
            if FStar_Syntax_Syntax.bv_eq bvar bv'
            then FStar_Pervasives_Native.Some (e', [])
            else
              (let uu____4291 = aux e'  in
               FStar_Util.map_opt uu____4291
                 (fun uu____4315  ->
                    match uu____4315 with | (e'',bvs) -> (e'', (bv' :: bvs))))
         in
      let uu____4336 = aux e  in
      FStar_Util.map_opt uu____4336
        (fun uu____4360  ->
           match uu____4360 with | (e',bvs) -> (e', (FStar_List.rev bvs)))
  
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
          let uu____4415 = split_env b1 g.FStar_Tactics_Types.context  in
          FStar_Util.map_opt uu____4415
            (fun uu____4439  ->
               match uu____4439 with
               | (e0,bvs) ->
                   let s1 bv =
                     let uu___87_4456 = bv  in
                     let uu____4457 =
                       FStar_Syntax_Subst.subst s bv.FStar_Syntax_Syntax.sort
                        in
                     {
                       FStar_Syntax_Syntax.ppname =
                         (uu___87_4456.FStar_Syntax_Syntax.ppname);
                       FStar_Syntax_Syntax.index =
                         (uu___87_4456.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort = uu____4457
                     }  in
                   let bvs1 = FStar_List.map s1 bvs  in
                   let c = push_bvs e0 (b2 :: bvs1)  in
                   let w =
                     FStar_Syntax_Subst.subst s g.FStar_Tactics_Types.witness
                      in
                   let t =
                     FStar_Syntax_Subst.subst s g.FStar_Tactics_Types.goal_ty
                      in
                   let uu___88_4466 = g  in
                   {
                     FStar_Tactics_Types.context = c;
                     FStar_Tactics_Types.witness = w;
                     FStar_Tactics_Types.goal_ty = t;
                     FStar_Tactics_Types.opts =
                       (uu___88_4466.FStar_Tactics_Types.opts);
                     FStar_Tactics_Types.is_guard =
                       (uu___88_4466.FStar_Tactics_Types.is_guard)
                   })
  
let (rewrite : FStar_Syntax_Syntax.binder -> Prims.unit tac) =
  fun h  ->
    bind cur_goal
      (fun goal  ->
         let uu____4479 = h  in
         match uu____4479 with
         | (bv,uu____4483) ->
             mlog
               (fun uu____4487  ->
                  let uu____4488 = FStar_Syntax_Print.bv_to_string bv  in
                  let uu____4489 =
                    tts goal.FStar_Tactics_Types.context
                      bv.FStar_Syntax_Syntax.sort
                     in
                  FStar_Util.print2 "+++Rewrite %s : %s\n" uu____4488
                    uu____4489)
               (fun uu____4492  ->
                  let uu____4493 =
                    split_env bv goal.FStar_Tactics_Types.context  in
                  match uu____4493 with
                  | FStar_Pervasives_Native.None  ->
                      fail "rewrite: binder not found in environment"
                  | FStar_Pervasives_Native.Some (e0,bvs) ->
                      let uu____4522 =
                        destruct_eq bv.FStar_Syntax_Syntax.sort  in
                      (match uu____4522 with
                       | FStar_Pervasives_Native.Some (x,e) ->
                           let uu____4537 =
                             let uu____4538 = FStar_Syntax_Subst.compress x
                                in
                             uu____4538.FStar_Syntax_Syntax.n  in
                           (match uu____4537 with
                            | FStar_Syntax_Syntax.Tm_name x1 ->
                                let s = [FStar_Syntax_Syntax.NT (x1, e)]  in
                                let s1 bv1 =
                                  let uu___89_4551 = bv1  in
                                  let uu____4552 =
                                    FStar_Syntax_Subst.subst s
                                      bv1.FStar_Syntax_Syntax.sort
                                     in
                                  {
                                    FStar_Syntax_Syntax.ppname =
                                      (uu___89_4551.FStar_Syntax_Syntax.ppname);
                                    FStar_Syntax_Syntax.index =
                                      (uu___89_4551.FStar_Syntax_Syntax.index);
                                    FStar_Syntax_Syntax.sort = uu____4552
                                  }  in
                                let bvs1 = FStar_List.map s1 bvs  in
                                let uu____4558 =
                                  let uu___90_4559 = goal  in
                                  let uu____4560 = push_bvs e0 (bv :: bvs1)
                                     in
                                  let uu____4561 =
                                    FStar_Syntax_Subst.subst s
                                      goal.FStar_Tactics_Types.witness
                                     in
                                  let uu____4562 =
                                    FStar_Syntax_Subst.subst s
                                      goal.FStar_Tactics_Types.goal_ty
                                     in
                                  {
                                    FStar_Tactics_Types.context = uu____4560;
                                    FStar_Tactics_Types.witness = uu____4561;
                                    FStar_Tactics_Types.goal_ty = uu____4562;
                                    FStar_Tactics_Types.opts =
                                      (uu___90_4559.FStar_Tactics_Types.opts);
                                    FStar_Tactics_Types.is_guard =
                                      (uu___90_4559.FStar_Tactics_Types.is_guard)
                                  }  in
                                replace_cur uu____4558
                            | uu____4563 ->
                                fail
                                  "rewrite: Not an equality hypothesis with a variable on the LHS")
                       | uu____4564 ->
                           fail "rewrite: Not an equality hypothesis")))
  
let (rename_to :
  FStar_Syntax_Syntax.binder -> Prims.string -> Prims.unit tac) =
  fun b  ->
    fun s  ->
      bind cur_goal
        (fun goal  ->
           let uu____4589 = b  in
           match uu____4589 with
           | (bv,uu____4593) ->
               let bv' =
                 FStar_Syntax_Syntax.freshen_bv
                   (let uu___91_4597 = bv  in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (FStar_Ident.mk_ident
                           (s,
                             ((bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange)));
                      FStar_Syntax_Syntax.index =
                        (uu___91_4597.FStar_Syntax_Syntax.index);
                      FStar_Syntax_Syntax.sort =
                        (uu___91_4597.FStar_Syntax_Syntax.sort)
                    })
                  in
               let s1 =
                 let uu____4601 =
                   let uu____4602 =
                     let uu____4609 = FStar_Syntax_Syntax.bv_to_name bv'  in
                     (bv, uu____4609)  in
                   FStar_Syntax_Syntax.NT uu____4602  in
                 [uu____4601]  in
               let uu____4610 = subst_goal bv bv' s1 goal  in
               (match uu____4610 with
                | FStar_Pervasives_Native.None  ->
                    fail "rename_to: binder not found in environment"
                | FStar_Pervasives_Native.Some goal1 -> replace_cur goal1))
  
let (binder_retype : FStar_Syntax_Syntax.binder -> Prims.unit tac) =
  fun b  ->
    bind cur_goal
      (fun goal  ->
         let uu____4629 = b  in
         match uu____4629 with
         | (bv,uu____4633) ->
             let uu____4634 = split_env bv goal.FStar_Tactics_Types.context
                in
             (match uu____4634 with
              | FStar_Pervasives_Native.None  ->
                  fail "binder_retype: binder is not present in environment"
              | FStar_Pervasives_Native.Some (e0,bvs) ->
                  let uu____4663 = FStar_Syntax_Util.type_u ()  in
                  (match uu____4663 with
                   | (ty,u) ->
                       let uu____4672 = new_uvar "binder_retype" e0 ty  in
                       bind uu____4672
                         (fun t'  ->
                            let bv'' =
                              let uu___92_4682 = bv  in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___92_4682.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___92_4682.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = t'
                              }  in
                            let s =
                              let uu____4686 =
                                let uu____4687 =
                                  let uu____4694 =
                                    FStar_Syntax_Syntax.bv_to_name bv''  in
                                  (bv, uu____4694)  in
                                FStar_Syntax_Syntax.NT uu____4687  in
                              [uu____4686]  in
                            let bvs1 =
                              FStar_List.map
                                (fun b1  ->
                                   let uu___93_4702 = b1  in
                                   let uu____4703 =
                                     FStar_Syntax_Subst.subst s
                                       b1.FStar_Syntax_Syntax.sort
                                      in
                                   {
                                     FStar_Syntax_Syntax.ppname =
                                       (uu___93_4702.FStar_Syntax_Syntax.ppname);
                                     FStar_Syntax_Syntax.index =
                                       (uu___93_4702.FStar_Syntax_Syntax.index);
                                     FStar_Syntax_Syntax.sort = uu____4703
                                   }) bvs
                               in
                            let env' = push_bvs e0 (bv'' :: bvs1)  in
                            bind dismiss
                              (fun uu____4709  ->
                                 let uu____4710 =
                                   let uu____4713 =
                                     let uu____4716 =
                                       let uu___94_4717 = goal  in
                                       let uu____4718 =
                                         FStar_Syntax_Subst.subst s
                                           goal.FStar_Tactics_Types.witness
                                          in
                                       let uu____4719 =
                                         FStar_Syntax_Subst.subst s
                                           goal.FStar_Tactics_Types.goal_ty
                                          in
                                       {
                                         FStar_Tactics_Types.context = env';
                                         FStar_Tactics_Types.witness =
                                           uu____4718;
                                         FStar_Tactics_Types.goal_ty =
                                           uu____4719;
                                         FStar_Tactics_Types.opts =
                                           (uu___94_4717.FStar_Tactics_Types.opts);
                                         FStar_Tactics_Types.is_guard =
                                           (uu___94_4717.FStar_Tactics_Types.is_guard)
                                       }  in
                                     [uu____4716]  in
                                   add_goals uu____4713  in
                                 bind uu____4710
                                   (fun uu____4722  ->
                                      let uu____4723 =
                                        FStar_Syntax_Util.mk_eq2
                                          (FStar_Syntax_Syntax.U_succ u) ty
                                          bv.FStar_Syntax_Syntax.sort t'
                                         in
                                      add_irrelevant_goal
                                        "binder_retype equation" e0
                                        uu____4723
                                        goal.FStar_Tactics_Types.opts))))))
  
let (norm_binder_type :
  FStar_Syntax_Embeddings.norm_step Prims.list ->
    FStar_Syntax_Syntax.binder -> Prims.unit tac)
  =
  fun s  ->
    fun b  ->
      bind cur_goal
        (fun goal  ->
           let uu____4744 = b  in
           match uu____4744 with
           | (bv,uu____4748) ->
               let uu____4749 = split_env bv goal.FStar_Tactics_Types.context
                  in
               (match uu____4749 with
                | FStar_Pervasives_Native.None  ->
                    fail
                      "binder_retype: binder is not present in environment"
                | FStar_Pervasives_Native.Some (e0,bvs) ->
                    let steps =
                      let uu____4781 =
                        FStar_TypeChecker_Normalize.tr_norm_steps s  in
                      FStar_List.append
                        [FStar_TypeChecker_Normalize.Reify;
                        FStar_TypeChecker_Normalize.UnfoldTac] uu____4781
                       in
                    let sort' =
                      normalize steps e0 bv.FStar_Syntax_Syntax.sort  in
                    let bv' =
                      let uu___95_4786 = bv  in
                      {
                        FStar_Syntax_Syntax.ppname =
                          (uu___95_4786.FStar_Syntax_Syntax.ppname);
                        FStar_Syntax_Syntax.index =
                          (uu___95_4786.FStar_Syntax_Syntax.index);
                        FStar_Syntax_Syntax.sort = sort'
                      }  in
                    let env' = push_bvs e0 (bv' :: bvs)  in
                    replace_cur
                      (let uu___96_4790 = goal  in
                       {
                         FStar_Tactics_Types.context = env';
                         FStar_Tactics_Types.witness =
                           (uu___96_4790.FStar_Tactics_Types.witness);
                         FStar_Tactics_Types.goal_ty =
                           (uu___96_4790.FStar_Tactics_Types.goal_ty);
                         FStar_Tactics_Types.opts =
                           (uu___96_4790.FStar_Tactics_Types.opts);
                         FStar_Tactics_Types.is_guard =
                           (uu___96_4790.FStar_Tactics_Types.is_guard)
                       })))
  
let (revert : Prims.unit tac) =
  bind cur_goal
    (fun goal  ->
       let uu____4798 =
         FStar_TypeChecker_Env.pop_bv goal.FStar_Tactics_Types.context  in
       match uu____4798 with
       | FStar_Pervasives_Native.None  -> fail "Cannot revert; empty context"
       | FStar_Pervasives_Native.Some (x,env') ->
           let typ' =
             let uu____4820 =
               FStar_Syntax_Syntax.mk_Total goal.FStar_Tactics_Types.goal_ty
                in
             FStar_Syntax_Util.arrow [(x, FStar_Pervasives_Native.None)]
               uu____4820
              in
           let w' =
             FStar_Syntax_Util.abs [(x, FStar_Pervasives_Native.None)]
               goal.FStar_Tactics_Types.witness FStar_Pervasives_Native.None
              in
           replace_cur
             (let uu___97_4854 = goal  in
              {
                FStar_Tactics_Types.context = env';
                FStar_Tactics_Types.witness = w';
                FStar_Tactics_Types.goal_ty = typ';
                FStar_Tactics_Types.opts =
                  (uu___97_4854.FStar_Tactics_Types.opts);
                FStar_Tactics_Types.is_guard =
                  (uu___97_4854.FStar_Tactics_Types.is_guard)
              }))
  
let (free_in :
  FStar_Syntax_Syntax.bv -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun bv  ->
    fun t  ->
      let uu____4861 = FStar_Syntax_Free.names t  in
      FStar_Util.set_mem bv uu____4861
  
let rec (clear : FStar_Syntax_Syntax.binder -> Prims.unit tac) =
  fun b  ->
    let bv = FStar_Pervasives_Native.fst b  in
    bind cur_goal
      (fun goal  ->
         mlog
           (fun uu____4877  ->
              let uu____4878 = FStar_Syntax_Print.binder_to_string b  in
              let uu____4879 =
                let uu____4880 =
                  let uu____4881 =
                    FStar_TypeChecker_Env.all_binders
                      goal.FStar_Tactics_Types.context
                     in
                  FStar_All.pipe_right uu____4881 FStar_List.length  in
                FStar_All.pipe_right uu____4880 FStar_Util.string_of_int  in
              FStar_Util.print2 "Clear of (%s), env has %s binders\n"
                uu____4878 uu____4879)
           (fun uu____4892  ->
              let uu____4893 = split_env bv goal.FStar_Tactics_Types.context
                 in
              match uu____4893 with
              | FStar_Pervasives_Native.None  ->
                  fail "Cannot clear; binder not in environment"
              | FStar_Pervasives_Native.Some (e',bvs) ->
                  let rec check bvs1 =
                    match bvs1 with
                    | [] -> ret ()
                    | bv'::bvs2 ->
                        let uu____4938 =
                          free_in bv bv'.FStar_Syntax_Syntax.sort  in
                        if uu____4938
                        then
                          let uu____4941 =
                            let uu____4942 =
                              FStar_Syntax_Print.bv_to_string bv'  in
                            FStar_Util.format1
                              "Cannot clear; binder present in the type of %s"
                              uu____4942
                             in
                          fail uu____4941
                        else check bvs2
                     in
                  let uu____4944 =
                    free_in bv goal.FStar_Tactics_Types.goal_ty  in
                  if uu____4944
                  then fail "Cannot clear; binder present in goal"
                  else
                    (let uu____4948 = check bvs  in
                     bind uu____4948
                       (fun uu____4954  ->
                          let env' = push_bvs e' bvs  in
                          let uu____4956 =
                            new_uvar "clear.witness" env'
                              goal.FStar_Tactics_Types.goal_ty
                             in
                          bind uu____4956
                            (fun ut  ->
                               let uu____4962 =
                                 do_unify goal.FStar_Tactics_Types.context
                                   goal.FStar_Tactics_Types.witness ut
                                  in
                               if uu____4962
                               then
                                 replace_cur
                                   (let uu___98_4967 = goal  in
                                    {
                                      FStar_Tactics_Types.context = env';
                                      FStar_Tactics_Types.witness = ut;
                                      FStar_Tactics_Types.goal_ty =
                                        (uu___98_4967.FStar_Tactics_Types.goal_ty);
                                      FStar_Tactics_Types.opts =
                                        (uu___98_4967.FStar_Tactics_Types.opts);
                                      FStar_Tactics_Types.is_guard =
                                        (uu___98_4967.FStar_Tactics_Types.is_guard)
                                    })
                               else
                                 fail
                                   "Cannot clear; binder appears in witness")))))
  
let (clear_top : Prims.unit tac) =
  bind cur_goal
    (fun goal  ->
       let uu____4976 =
         FStar_TypeChecker_Env.pop_bv goal.FStar_Tactics_Types.context  in
       match uu____4976 with
       | FStar_Pervasives_Native.None  -> fail "Cannot clear; empty context"
       | FStar_Pervasives_Native.Some (x,uu____4990) ->
           let uu____4995 = FStar_Syntax_Syntax.mk_binder x  in
           clear uu____4995)
  
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
           let uu___99_5011 = g  in
           {
             FStar_Tactics_Types.context = ctx';
             FStar_Tactics_Types.witness =
               (uu___99_5011.FStar_Tactics_Types.witness);
             FStar_Tactics_Types.goal_ty =
               (uu___99_5011.FStar_Tactics_Types.goal_ty);
             FStar_Tactics_Types.opts =
               (uu___99_5011.FStar_Tactics_Types.opts);
             FStar_Tactics_Types.is_guard =
               (uu___99_5011.FStar_Tactics_Types.is_guard)
           }  in
         bind dismiss (fun uu____5013  -> add_goals [g']))
  
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
           let uu___100_5029 = g  in
           {
             FStar_Tactics_Types.context = ctx';
             FStar_Tactics_Types.witness =
               (uu___100_5029.FStar_Tactics_Types.witness);
             FStar_Tactics_Types.goal_ty =
               (uu___100_5029.FStar_Tactics_Types.goal_ty);
             FStar_Tactics_Types.opts =
               (uu___100_5029.FStar_Tactics_Types.opts);
             FStar_Tactics_Types.is_guard =
               (uu___100_5029.FStar_Tactics_Types.is_guard)
           }  in
         bind dismiss (fun uu____5031  -> add_goals [g']))
  
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
            let uu____5063 = FStar_Syntax_Subst.compress t  in
            uu____5063.FStar_Syntax_Syntax.n  in
          let uu____5066 =
            if d = FStar_Tactics_Types.TopDown
            then
              f env
                (let uu___102_5072 = t  in
                 {
                   FStar_Syntax_Syntax.n = tn;
                   FStar_Syntax_Syntax.pos =
                     (uu___102_5072.FStar_Syntax_Syntax.pos);
                   FStar_Syntax_Syntax.vars =
                     (uu___102_5072.FStar_Syntax_Syntax.vars)
                 })
            else ret t  in
          bind uu____5066
            (fun t1  ->
               let tn1 =
                 let uu____5080 =
                   let uu____5081 = FStar_Syntax_Subst.compress t1  in
                   uu____5081.FStar_Syntax_Syntax.n  in
                 match uu____5080 with
                 | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
                     let ff = tac_fold_env d f env  in
                     let uu____5113 = ff hd1  in
                     bind uu____5113
                       (fun hd2  ->
                          let fa uu____5133 =
                            match uu____5133 with
                            | (a,q) ->
                                let uu____5146 = ff a  in
                                bind uu____5146 (fun a1  -> ret (a1, q))
                             in
                          let uu____5159 = mapM fa args  in
                          bind uu____5159
                            (fun args1  ->
                               ret (FStar_Syntax_Syntax.Tm_app (hd2, args1))))
                 | FStar_Syntax_Syntax.Tm_abs (bs,t2,k) ->
                     let uu____5219 = FStar_Syntax_Subst.open_term bs t2  in
                     (match uu____5219 with
                      | (bs1,t') ->
                          let uu____5228 =
                            let uu____5231 =
                              FStar_TypeChecker_Env.push_binders env bs1  in
                            tac_fold_env d f uu____5231 t'  in
                          bind uu____5228
                            (fun t''  ->
                               let uu____5235 =
                                 let uu____5236 =
                                   let uu____5253 =
                                     FStar_Syntax_Subst.close_binders bs1  in
                                   let uu____5254 =
                                     FStar_Syntax_Subst.close bs1 t''  in
                                   (uu____5253, uu____5254, k)  in
                                 FStar_Syntax_Syntax.Tm_abs uu____5236  in
                               ret uu____5235))
                 | FStar_Syntax_Syntax.Tm_arrow (bs,k) -> ret tn
                 | uu____5275 -> ret tn  in
               bind tn1
                 (fun tn2  ->
                    let t' =
                      let uu___101_5282 = t1  in
                      {
                        FStar_Syntax_Syntax.n = tn2;
                        FStar_Syntax_Syntax.pos =
                          (uu___101_5282.FStar_Syntax_Syntax.pos);
                        FStar_Syntax_Syntax.vars =
                          (uu___101_5282.FStar_Syntax_Syntax.vars)
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
            let uu____5311 = FStar_TypeChecker_TcTerm.tc_term env t  in
            match uu____5311 with
            | (t1,lcomp,g) ->
                let uu____5323 =
                  (let uu____5326 =
                     FStar_Syntax_Util.is_pure_or_ghost_lcomp lcomp  in
                   Prims.op_Negation uu____5326) ||
                    (let uu____5328 = FStar_TypeChecker_Rel.is_trivial g  in
                     Prims.op_Negation uu____5328)
                   in
                if uu____5323
                then ret t1
                else
                  (let rewrite_eq =
                     let typ = lcomp.FStar_Syntax_Syntax.res_typ  in
                     let uu____5338 = new_uvar "pointwise_rec" env typ  in
                     bind uu____5338
                       (fun ut  ->
                          log ps
                            (fun uu____5349  ->
                               let uu____5350 =
                                 FStar_Syntax_Print.term_to_string t1  in
                               let uu____5351 =
                                 FStar_Syntax_Print.term_to_string ut  in
                               FStar_Util.print2
                                 "Pointwise_rec: making equality\n\t%s ==\n\t%s\n"
                                 uu____5350 uu____5351);
                          (let uu____5352 =
                             let uu____5355 =
                               let uu____5356 =
                                 FStar_TypeChecker_TcTerm.universe_of env typ
                                  in
                               FStar_Syntax_Util.mk_eq2 uu____5356 typ t1 ut
                                in
                             add_irrelevant_goal "pointwise_rec equation" env
                               uu____5355 opts
                              in
                           bind uu____5352
                             (fun uu____5359  ->
                                let uu____5360 =
                                  bind tau
                                    (fun uu____5366  ->
                                       let ut1 =
                                         FStar_TypeChecker_Normalize.reduce_uvar_solutions
                                           env ut
                                          in
                                       log ps
                                         (fun uu____5372  ->
                                            let uu____5373 =
                                              FStar_Syntax_Print.term_to_string
                                                t1
                                               in
                                            let uu____5374 =
                                              FStar_Syntax_Print.term_to_string
                                                ut1
                                               in
                                            FStar_Util.print2
                                              "Pointwise_rec: succeeded rewriting\n\t%s to\n\t%s\n"
                                              uu____5373 uu____5374);
                                       ret ut1)
                                   in
                                focus uu____5360)))
                      in
                   let uu____5375 = trytac' rewrite_eq  in
                   bind uu____5375
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
           let uu____5417 =
             match ps.FStar_Tactics_Types.goals with
             | g::gs -> (g, gs)
             | [] -> failwith "Pointwise: no goals"  in
           match uu____5417 with
           | (g,gs) ->
               let gt1 = g.FStar_Tactics_Types.goal_ty  in
               (log ps
                  (fun uu____5454  ->
                     let uu____5455 = FStar_Syntax_Print.term_to_string gt1
                        in
                     FStar_Util.print1 "Pointwise starting with %s\n"
                       uu____5455);
                bind dismiss_all
                  (fun uu____5458  ->
                     let uu____5459 =
                       tac_fold_env d
                         (pointwise_rec ps tau g.FStar_Tactics_Types.opts)
                         g.FStar_Tactics_Types.context gt1
                        in
                     bind uu____5459
                       (fun gt'  ->
                          log ps
                            (fun uu____5469  ->
                               let uu____5470 =
                                 FStar_Syntax_Print.term_to_string gt'  in
                               FStar_Util.print1
                                 "Pointwise seems to have succeded with %s\n"
                                 uu____5470);
                          (let uu____5471 = push_goals gs  in
                           bind uu____5471
                             (fun uu____5475  ->
                                add_goals
                                  [(let uu___103_5477 = g  in
                                    {
                                      FStar_Tactics_Types.context =
                                        (uu___103_5477.FStar_Tactics_Types.context);
                                      FStar_Tactics_Types.witness =
                                        (uu___103_5477.FStar_Tactics_Types.witness);
                                      FStar_Tactics_Types.goal_ty = gt';
                                      FStar_Tactics_Types.opts =
                                        (uu___103_5477.FStar_Tactics_Types.opts);
                                      FStar_Tactics_Types.is_guard =
                                        (uu___103_5477.FStar_Tactics_Types.is_guard)
                                    })]))))))
  
let (trefl : Prims.unit tac) =
  bind cur_goal
    (fun g  ->
       let uu____5499 =
         FStar_Syntax_Util.un_squash g.FStar_Tactics_Types.goal_ty  in
       match uu____5499 with
       | FStar_Pervasives_Native.Some t ->
           let uu____5511 = FStar_Syntax_Util.head_and_args' t  in
           (match uu____5511 with
            | (hd1,args) ->
                let uu____5544 =
                  let uu____5557 =
                    let uu____5558 = FStar_Syntax_Util.un_uinst hd1  in
                    uu____5558.FStar_Syntax_Syntax.n  in
                  (uu____5557, args)  in
                (match uu____5544 with
                 | (FStar_Syntax_Syntax.Tm_fvar
                    fv,uu____5572::(l,uu____5574)::(r,uu____5576)::[]) when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.eq2_lid
                     ->
                     let uu____5623 =
                       let uu____5624 =
                         do_unify g.FStar_Tactics_Types.context l r  in
                       Prims.op_Negation uu____5624  in
                     if uu____5623
                     then
                       let uu____5627 = tts g.FStar_Tactics_Types.context l
                          in
                       let uu____5628 = tts g.FStar_Tactics_Types.context r
                          in
                       fail2 "trefl: not a trivial equality (%s vs %s)"
                         uu____5627 uu____5628
                     else solve g FStar_Syntax_Util.exp_unit
                 | (hd2,uu____5631) ->
                     let uu____5648 = tts g.FStar_Tactics_Types.context t  in
                     fail1 "trefl: not an equality (%s)" uu____5648))
       | FStar_Pervasives_Native.None  -> fail "not an irrelevant goal")
  
let (dup : Prims.unit tac) =
  bind cur_goal
    (fun g  ->
       let uu____5658 =
         new_uvar "dup" g.FStar_Tactics_Types.context
           g.FStar_Tactics_Types.goal_ty
          in
       bind uu____5658
         (fun u  ->
            let g' =
              let uu___104_5665 = g  in
              {
                FStar_Tactics_Types.context =
                  (uu___104_5665.FStar_Tactics_Types.context);
                FStar_Tactics_Types.witness = u;
                FStar_Tactics_Types.goal_ty =
                  (uu___104_5665.FStar_Tactics_Types.goal_ty);
                FStar_Tactics_Types.opts =
                  (uu___104_5665.FStar_Tactics_Types.opts);
                FStar_Tactics_Types.is_guard =
                  (uu___104_5665.FStar_Tactics_Types.is_guard)
              }  in
            bind dismiss
              (fun uu____5668  ->
                 let uu____5669 =
                   let uu____5672 =
                     let uu____5673 =
                       FStar_TypeChecker_TcTerm.universe_of
                         g.FStar_Tactics_Types.context
                         g.FStar_Tactics_Types.goal_ty
                        in
                     FStar_Syntax_Util.mk_eq2 uu____5673
                       g.FStar_Tactics_Types.goal_ty u
                       g.FStar_Tactics_Types.witness
                      in
                   add_irrelevant_goal "dup equation"
                     g.FStar_Tactics_Types.context uu____5672
                     g.FStar_Tactics_Types.opts
                    in
                 bind uu____5669
                   (fun uu____5676  ->
                      let uu____5677 = add_goals [g']  in
                      bind uu____5677 (fun uu____5681  -> ret ())))))
  
let (flip : Prims.unit tac) =
  bind get
    (fun ps  ->
       match ps.FStar_Tactics_Types.goals with
       | g1::g2::gs ->
           set
             (let uu___105_5700 = ps  in
              {
                FStar_Tactics_Types.main_context =
                  (uu___105_5700.FStar_Tactics_Types.main_context);
                FStar_Tactics_Types.main_goal =
                  (uu___105_5700.FStar_Tactics_Types.main_goal);
                FStar_Tactics_Types.all_implicits =
                  (uu___105_5700.FStar_Tactics_Types.all_implicits);
                FStar_Tactics_Types.goals = (g2 :: g1 :: gs);
                FStar_Tactics_Types.smt_goals =
                  (uu___105_5700.FStar_Tactics_Types.smt_goals);
                FStar_Tactics_Types.depth =
                  (uu___105_5700.FStar_Tactics_Types.depth);
                FStar_Tactics_Types.__dump =
                  (uu___105_5700.FStar_Tactics_Types.__dump);
                FStar_Tactics_Types.psc =
                  (uu___105_5700.FStar_Tactics_Types.psc);
                FStar_Tactics_Types.entry_range =
                  (uu___105_5700.FStar_Tactics_Types.entry_range)
              })
       | uu____5701 -> fail "flip: less than 2 goals")
  
let (later : Prims.unit tac) =
  bind get
    (fun ps  ->
       match ps.FStar_Tactics_Types.goals with
       | [] -> ret ()
       | g::gs ->
           set
             (let uu___106_5718 = ps  in
              {
                FStar_Tactics_Types.main_context =
                  (uu___106_5718.FStar_Tactics_Types.main_context);
                FStar_Tactics_Types.main_goal =
                  (uu___106_5718.FStar_Tactics_Types.main_goal);
                FStar_Tactics_Types.all_implicits =
                  (uu___106_5718.FStar_Tactics_Types.all_implicits);
                FStar_Tactics_Types.goals = (FStar_List.append gs [g]);
                FStar_Tactics_Types.smt_goals =
                  (uu___106_5718.FStar_Tactics_Types.smt_goals);
                FStar_Tactics_Types.depth =
                  (uu___106_5718.FStar_Tactics_Types.depth);
                FStar_Tactics_Types.__dump =
                  (uu___106_5718.FStar_Tactics_Types.__dump);
                FStar_Tactics_Types.psc =
                  (uu___106_5718.FStar_Tactics_Types.psc);
                FStar_Tactics_Types.entry_range =
                  (uu___106_5718.FStar_Tactics_Types.entry_range)
              }))
  
let (qed : Prims.unit tac) =
  bind get
    (fun ps  ->
       match ps.FStar_Tactics_Types.goals with
       | [] -> ret ()
       | uu____5727 -> fail "Not done!")
  
let (cases :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 tac)
  =
  fun t  ->
    let uu____5745 =
      bind cur_goal
        (fun g  ->
           let uu____5759 = __tc g.FStar_Tactics_Types.context t  in
           bind uu____5759
             (fun uu____5795  ->
                match uu____5795 with
                | (t1,typ,guard) ->
                    let uu____5811 = FStar_Syntax_Util.head_and_args typ  in
                    (match uu____5811 with
                     | (hd1,args) ->
                         let uu____5854 =
                           let uu____5867 =
                             let uu____5868 = FStar_Syntax_Util.un_uinst hd1
                                in
                             uu____5868.FStar_Syntax_Syntax.n  in
                           (uu____5867, args)  in
                         (match uu____5854 with
                          | (FStar_Syntax_Syntax.Tm_fvar
                             fv,(p,uu____5887)::(q,uu____5889)::[]) when
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
                                let uu___107_5927 = g  in
                                let uu____5928 =
                                  FStar_TypeChecker_Env.push_bv
                                    g.FStar_Tactics_Types.context v_p
                                   in
                                {
                                  FStar_Tactics_Types.context = uu____5928;
                                  FStar_Tactics_Types.witness =
                                    (uu___107_5927.FStar_Tactics_Types.witness);
                                  FStar_Tactics_Types.goal_ty =
                                    (uu___107_5927.FStar_Tactics_Types.goal_ty);
                                  FStar_Tactics_Types.opts =
                                    (uu___107_5927.FStar_Tactics_Types.opts);
                                  FStar_Tactics_Types.is_guard =
                                    (uu___107_5927.FStar_Tactics_Types.is_guard)
                                }  in
                              let g2 =
                                let uu___108_5930 = g  in
                                let uu____5931 =
                                  FStar_TypeChecker_Env.push_bv
                                    g.FStar_Tactics_Types.context v_q
                                   in
                                {
                                  FStar_Tactics_Types.context = uu____5931;
                                  FStar_Tactics_Types.witness =
                                    (uu___108_5930.FStar_Tactics_Types.witness);
                                  FStar_Tactics_Types.goal_ty =
                                    (uu___108_5930.FStar_Tactics_Types.goal_ty);
                                  FStar_Tactics_Types.opts =
                                    (uu___108_5930.FStar_Tactics_Types.opts);
                                  FStar_Tactics_Types.is_guard =
                                    (uu___108_5930.FStar_Tactics_Types.is_guard)
                                }  in
                              bind dismiss
                                (fun uu____5938  ->
                                   let uu____5939 = add_goals [g1; g2]  in
                                   bind uu____5939
                                     (fun uu____5948  ->
                                        let uu____5949 =
                                          let uu____5954 =
                                            FStar_Syntax_Syntax.bv_to_name
                                              v_p
                                             in
                                          let uu____5955 =
                                            FStar_Syntax_Syntax.bv_to_name
                                              v_q
                                             in
                                          (uu____5954, uu____5955)  in
                                        ret uu____5949))
                          | uu____5960 ->
                              let uu____5973 =
                                tts g.FStar_Tactics_Types.context typ  in
                              fail1 "Not a disjunction: %s" uu____5973))))
       in
    FStar_All.pipe_left (wrap_err "cases") uu____5745
  
let (set_options : Prims.string -> Prims.unit tac) =
  fun s  ->
    bind cur_goal
      (fun g  ->
         FStar_Options.push ();
         (let uu____6011 = FStar_Util.smap_copy g.FStar_Tactics_Types.opts
             in
          FStar_Options.set uu____6011);
         (let res = FStar_Options.set_options FStar_Options.Set s  in
          let opts' = FStar_Options.peek ()  in
          FStar_Options.pop ();
          (match res with
           | FStar_Getopt.Success  ->
               let g' =
                 let uu___109_6018 = g  in
                 {
                   FStar_Tactics_Types.context =
                     (uu___109_6018.FStar_Tactics_Types.context);
                   FStar_Tactics_Types.witness =
                     (uu___109_6018.FStar_Tactics_Types.witness);
                   FStar_Tactics_Types.goal_ty =
                     (uu___109_6018.FStar_Tactics_Types.goal_ty);
                   FStar_Tactics_Types.opts = opts';
                   FStar_Tactics_Types.is_guard =
                     (uu___109_6018.FStar_Tactics_Types.is_guard)
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
      let uu____6062 =
        bind cur_goal
          (fun goal  ->
             let env =
               FStar_TypeChecker_Env.set_expected_typ
                 goal.FStar_Tactics_Types.context ty
                in
             let uu____6070 = __tc env tm  in
             bind uu____6070
               (fun uu____6090  ->
                  match uu____6090 with
                  | (tm1,typ,guard) ->
                      (FStar_TypeChecker_Rel.force_trivial_guard env guard;
                       ret tm1)))
         in
      FStar_All.pipe_left (wrap_err "unquote") uu____6062
  
let (uvar_env :
  env ->
    FStar_Syntax_Syntax.typ FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.term tac)
  =
  fun env  ->
    fun ty  ->
      let uu____6121 =
        match ty with
        | FStar_Pervasives_Native.Some ty1 -> ret ty1
        | FStar_Pervasives_Native.None  ->
            let uu____6127 =
              let uu____6128 = FStar_Syntax_Util.type_u ()  in
              FStar_All.pipe_left FStar_Pervasives_Native.fst uu____6128  in
            new_uvar "uvar_env.2" env uu____6127
         in
      bind uu____6121
        (fun typ  ->
           let uu____6140 = new_uvar "uvar_env" env typ  in
           bind uu____6140 (fun t  -> ret t))
  
let (unshelve : FStar_Syntax_Syntax.term -> Prims.unit tac) =
  fun t  ->
    let uu____6152 =
      bind cur_goal
        (fun goal  ->
           let uu____6158 = __tc goal.FStar_Tactics_Types.context t  in
           bind uu____6158
             (fun uu____6178  ->
                match uu____6178 with
                | (t1,typ,guard) ->
                    let uu____6190 =
                      must_trivial goal.FStar_Tactics_Types.context guard  in
                    bind uu____6190
                      (fun uu____6195  ->
                         let uu____6196 =
                           let uu____6199 =
                             let uu___110_6200 = goal  in
                             let uu____6201 =
                               bnorm goal.FStar_Tactics_Types.context t1  in
                             let uu____6202 =
                               bnorm goal.FStar_Tactics_Types.context typ  in
                             {
                               FStar_Tactics_Types.context =
                                 (uu___110_6200.FStar_Tactics_Types.context);
                               FStar_Tactics_Types.witness = uu____6201;
                               FStar_Tactics_Types.goal_ty = uu____6202;
                               FStar_Tactics_Types.opts =
                                 (uu___110_6200.FStar_Tactics_Types.opts);
                               FStar_Tactics_Types.is_guard = false
                             }  in
                           [uu____6199]  in
                         add_goals uu____6196)))
       in
    FStar_All.pipe_left (wrap_err "unshelve") uu____6152
  
let (unify :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool tac) =
  fun t1  ->
    fun t2  ->
      bind get
        (fun ps  ->
           let uu____6220 =
             do_unify ps.FStar_Tactics_Types.main_context t1 t2  in
           ret uu____6220)
  
let (launch_process :
  Prims.string -> Prims.string -> Prims.string -> Prims.string tac) =
  fun prog  ->
    fun args  ->
      fun input  ->
        bind idtac
          (fun uu____6237  ->
             let uu____6238 = FStar_Options.unsafe_tactic_exec ()  in
             if uu____6238
             then
               let s =
                 FStar_Util.launch_process true "tactic_launch" prog args
                   input (fun uu____6244  -> fun uu____6245  -> false)
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
      let uu____6261 =
        FStar_TypeChecker_Util.new_implicit_var "proofstate_of_goal_ty"
          typ.FStar_Syntax_Syntax.pos env typ
         in
      match uu____6261 with
      | (u,uu____6279,g_u) ->
          let g =
            let uu____6294 = FStar_Options.peek ()  in
            {
              FStar_Tactics_Types.context = env;
              FStar_Tactics_Types.witness = u;
              FStar_Tactics_Types.goal_ty = typ;
              FStar_Tactics_Types.opts = uu____6294;
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
      let uu____6305 = goal_of_goal_ty env typ  in
      match uu____6305 with
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
  