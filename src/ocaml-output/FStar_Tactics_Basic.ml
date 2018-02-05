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
  
let trytac' : 'a . 'a tac -> (Prims.string,'a) FStar_Util.either tac =
  fun t  ->
    mk_tac
      (fun ps  ->
         let tx = FStar_Syntax_Unionfind.new_transaction ()  in
         let uu____721 = run t ps  in
         match uu____721 with
         | FStar_Tactics_Result.Success (a,q) ->
             (FStar_Syntax_Unionfind.commit tx;
              FStar_Tactics_Result.Success ((FStar_Util.Inr a), q))
         | FStar_Tactics_Result.Failed (m,uu____742) ->
             (FStar_Syntax_Unionfind.rollback tx;
              FStar_Tactics_Result.Success ((FStar_Util.Inl m), ps)))
  
let trytac : 'a . 'a tac -> 'a FStar_Pervasives_Native.option tac =
  fun t  ->
    let uu____767 = trytac' t  in
    bind uu____767
      (fun r  ->
         match r with
         | FStar_Util.Inr v1 -> ret (FStar_Pervasives_Native.Some v1)
         | FStar_Util.Inl uu____794 -> ret FStar_Pervasives_Native.None)
  
let wrap_err : 'a . Prims.string -> 'a tac -> 'a tac =
  fun pref  ->
    fun t  ->
      mk_tac
        (fun ps  ->
           let uu____820 = run t ps  in
           match uu____820 with
           | FStar_Tactics_Result.Success (a,q) ->
               FStar_Tactics_Result.Success (a, q)
           | FStar_Tactics_Result.Failed (msg,q) ->
               FStar_Tactics_Result.Failed
                 ((Prims.strcat pref (Prims.strcat ": " msg)), q))
  
let (set : FStar_Tactics_Types.proofstate -> Prims.unit tac) =
  fun p  -> mk_tac (fun uu____837  -> FStar_Tactics_Result.Success ((), p)) 
let (do_unify :
  env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let debug_on uu____850 =
          let uu____851 =
            FStar_Options.set_options FStar_Options.Set
              "--debug_level Rel --debug_level RelCheck"
             in
          ()  in
        let debug_off uu____855 =
          let uu____856 = FStar_Options.set_options FStar_Options.Reset ""
             in
          ()  in
        (let uu____858 =
           FStar_TypeChecker_Env.debug env (FStar_Options.Other "1346")  in
         if uu____858
         then
           (debug_on ();
            (let uu____860 = FStar_Syntax_Print.term_to_string t1  in
             let uu____861 = FStar_Syntax_Print.term_to_string t2  in
             FStar_Util.print2 "%%%%%%%%do_unify %s =? %s\n" uu____860
               uu____861))
         else ());
        (try
           let res = FStar_TypeChecker_Rel.teq_nosmt env t1 t2  in
           debug_off (); res
         with | uu____873 -> (debug_off (); false))
  
let (trysolve :
  FStar_Tactics_Types.goal -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun goal  ->
    fun solution  ->
      do_unify goal.FStar_Tactics_Types.context solution
        goal.FStar_Tactics_Types.witness
  
let (dismiss : Prims.unit tac) =
  bind get
    (fun p  ->
       let uu____886 =
         let uu___62_887 = p  in
         let uu____888 = FStar_List.tl p.FStar_Tactics_Types.goals  in
         {
           FStar_Tactics_Types.main_context =
             (uu___62_887.FStar_Tactics_Types.main_context);
           FStar_Tactics_Types.main_goal =
             (uu___62_887.FStar_Tactics_Types.main_goal);
           FStar_Tactics_Types.all_implicits =
             (uu___62_887.FStar_Tactics_Types.all_implicits);
           FStar_Tactics_Types.goals = uu____888;
           FStar_Tactics_Types.smt_goals =
             (uu___62_887.FStar_Tactics_Types.smt_goals);
           FStar_Tactics_Types.depth =
             (uu___62_887.FStar_Tactics_Types.depth);
           FStar_Tactics_Types.__dump =
             (uu___62_887.FStar_Tactics_Types.__dump);
           FStar_Tactics_Types.psc = (uu___62_887.FStar_Tactics_Types.psc);
           FStar_Tactics_Types.entry_range =
             (uu___62_887.FStar_Tactics_Types.entry_range)
         }  in
       set uu____886)
  
let (solve :
  FStar_Tactics_Types.goal -> FStar_Syntax_Syntax.term -> Prims.unit tac) =
  fun goal  ->
    fun solution  ->
      let uu____901 = trysolve goal solution  in
      if uu____901
      then dismiss
      else
        (let uu____905 =
           let uu____906 = tts goal.FStar_Tactics_Types.context solution  in
           let uu____907 =
             tts goal.FStar_Tactics_Types.context
               goal.FStar_Tactics_Types.witness
              in
           let uu____908 =
             tts goal.FStar_Tactics_Types.context
               goal.FStar_Tactics_Types.goal_ty
              in
           FStar_Util.format3 "%s does not solve %s : %s" uu____906 uu____907
             uu____908
            in
         fail uu____905)
  
let (dismiss_all : Prims.unit tac) =
  bind get
    (fun p  ->
       set
         (let uu___63_915 = p  in
          {
            FStar_Tactics_Types.main_context =
              (uu___63_915.FStar_Tactics_Types.main_context);
            FStar_Tactics_Types.main_goal =
              (uu___63_915.FStar_Tactics_Types.main_goal);
            FStar_Tactics_Types.all_implicits =
              (uu___63_915.FStar_Tactics_Types.all_implicits);
            FStar_Tactics_Types.goals = [];
            FStar_Tactics_Types.smt_goals =
              (uu___63_915.FStar_Tactics_Types.smt_goals);
            FStar_Tactics_Types.depth =
              (uu___63_915.FStar_Tactics_Types.depth);
            FStar_Tactics_Types.__dump =
              (uu___63_915.FStar_Tactics_Types.__dump);
            FStar_Tactics_Types.psc = (uu___63_915.FStar_Tactics_Types.psc);
            FStar_Tactics_Types.entry_range =
              (uu___63_915.FStar_Tactics_Types.entry_range)
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
      let uu____943 = FStar_TypeChecker_Env.pop_bv e  in
      match uu____943 with
      | FStar_Pervasives_Native.None  -> b3
      | FStar_Pervasives_Native.Some (bv,e1) ->
          let b4 =
            b3 &&
              (FStar_TypeChecker_Env.closed e1 bv.FStar_Syntax_Syntax.sort)
             in
          aux b4 e1
       in
    let uu____961 =
      (let uu____964 = aux b2 env  in Prims.op_Negation uu____964) &&
        (let uu____966 = FStar_ST.op_Bang nwarn  in
         uu____966 < (Prims.parse_int "5"))
       in
    if uu____961
    then
      ((let uu____987 =
          let uu____992 =
            let uu____993 = goal_to_string g  in
            FStar_Util.format1
              "The following goal is ill-formed. Keeping calm and carrying on...\n<%s>\n\n"
              uu____993
             in
          (FStar_Errors.Warning_IllFormedGoal, uu____992)  in
        FStar_Errors.log_issue
          (g.FStar_Tactics_Types.goal_ty).FStar_Syntax_Syntax.pos uu____987);
       (let uu____994 =
          let uu____995 = FStar_ST.op_Bang nwarn  in
          uu____995 + (Prims.parse_int "1")  in
        FStar_ST.op_Colon_Equals nwarn uu____994))
    else ()
  
let (add_goals : FStar_Tactics_Types.goal Prims.list -> Prims.unit tac) =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___64_1052 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___64_1052.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___64_1052.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___64_1052.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (FStar_List.append gs p.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___64_1052.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___64_1052.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___64_1052.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___64_1052.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___64_1052.FStar_Tactics_Types.entry_range)
            }))
  
let (add_smt_goals : FStar_Tactics_Types.goal Prims.list -> Prims.unit tac) =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___65_1070 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___65_1070.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___65_1070.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___65_1070.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___65_1070.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (FStar_List.append gs p.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___65_1070.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___65_1070.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___65_1070.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___65_1070.FStar_Tactics_Types.entry_range)
            }))
  
let (push_goals : FStar_Tactics_Types.goal Prims.list -> Prims.unit tac) =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___66_1088 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___66_1088.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___66_1088.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___66_1088.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (FStar_List.append p.FStar_Tactics_Types.goals gs);
              FStar_Tactics_Types.smt_goals =
                (uu___66_1088.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___66_1088.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___66_1088.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___66_1088.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___66_1088.FStar_Tactics_Types.entry_range)
            }))
  
let (push_smt_goals : FStar_Tactics_Types.goal Prims.list -> Prims.unit tac)
  =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___67_1106 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___67_1106.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___67_1106.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___67_1106.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___67_1106.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (FStar_List.append p.FStar_Tactics_Types.smt_goals gs);
              FStar_Tactics_Types.depth =
                (uu___67_1106.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___67_1106.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___67_1106.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___67_1106.FStar_Tactics_Types.entry_range)
            }))
  
let (replace_cur : FStar_Tactics_Types.goal -> Prims.unit tac) =
  fun g  -> bind dismiss (fun uu____1115  -> add_goals [g]) 
let (add_implicits : implicits -> Prims.unit tac) =
  fun i  ->
    bind get
      (fun p  ->
         set
           (let uu___68_1127 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___68_1127.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___68_1127.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (FStar_List.append i p.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___68_1127.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___68_1127.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___68_1127.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___68_1127.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___68_1127.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___68_1127.FStar_Tactics_Types.entry_range)
            }))
  
let (new_uvar :
  Prims.string ->
    env -> FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.term tac)
  =
  fun reason  ->
    fun env  ->
      fun typ  ->
        let uu____1153 =
          FStar_TypeChecker_Util.new_implicit_var reason
            typ.FStar_Syntax_Syntax.pos env typ
           in
        match uu____1153 with
        | (u,uu____1169,g_u) ->
            let uu____1183 =
              add_implicits g_u.FStar_TypeChecker_Env.implicits  in
            bind uu____1183 (fun uu____1187  -> ret u)
  
let (is_true : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____1191 = FStar_Syntax_Util.un_squash t  in
    match uu____1191 with
    | FStar_Pervasives_Native.Some t' ->
        let uu____1201 =
          let uu____1202 = FStar_Syntax_Subst.compress t'  in
          uu____1202.FStar_Syntax_Syntax.n  in
        (match uu____1201 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.true_lid
         | uu____1206 -> false)
    | uu____1207 -> false
  
let (is_false : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____1215 = FStar_Syntax_Util.un_squash t  in
    match uu____1215 with
    | FStar_Pervasives_Native.Some t' ->
        let uu____1225 =
          let uu____1226 = FStar_Syntax_Subst.compress t'  in
          uu____1226.FStar_Syntax_Syntax.n  in
        (match uu____1225 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.false_lid
         | uu____1230 -> false)
    | uu____1231 -> false
  
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
            let uu____1271 = env.FStar_TypeChecker_Env.universe_of env phi
               in
            FStar_Syntax_Util.mk_squash uu____1271 phi  in
          let uu____1272 = new_uvar reason env typ  in
          bind uu____1272
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
             let uu____1328 =
               (ps.FStar_Tactics_Types.main_context).FStar_TypeChecker_Env.type_of
                 e t
                in
             ret uu____1328
           with | e1 -> fail "not typeable")
  
let (must_trivial : env -> FStar_TypeChecker_Env.guard_t -> Prims.unit tac) =
  fun e  ->
    fun g  ->
      try
        let uu____1376 =
          let uu____1377 =
            let uu____1378 = FStar_TypeChecker_Rel.discharge_guard_no_smt e g
               in
            FStar_All.pipe_left FStar_TypeChecker_Rel.is_trivial uu____1378
             in
          Prims.op_Negation uu____1377  in
        if uu____1376 then fail "got non-trivial guard" else ret ()
      with | uu____1387 -> fail "got non-trivial guard"
  
let (tc : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.typ tac) =
  fun t  ->
    let uu____1395 =
      bind cur_goal
        (fun goal  ->
           let uu____1401 = __tc goal.FStar_Tactics_Types.context t  in
           bind uu____1401
             (fun uu____1421  ->
                match uu____1421 with
                | (t1,typ,guard) ->
                    let uu____1433 =
                      must_trivial goal.FStar_Tactics_Types.context guard  in
                    bind uu____1433 (fun uu____1437  -> ret typ)))
       in
    FStar_All.pipe_left (wrap_err "tc") uu____1395
  
let (add_irrelevant_goal :
  Prims.string ->
    env ->
      FStar_Syntax_Syntax.typ -> FStar_Options.optionstate -> Prims.unit tac)
  =
  fun reason  ->
    fun env  ->
      fun phi  ->
        fun opts  ->
          let uu____1458 = mk_irrelevant_goal reason env phi opts  in
          bind uu____1458 (fun goal  -> add_goals [goal])
  
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
       let uu____1480 =
         istrivial goal.FStar_Tactics_Types.context
           goal.FStar_Tactics_Types.goal_ty
          in
       if uu____1480
       then solve goal FStar_Syntax_Util.exp_unit
       else
         (let uu____1484 =
            tts goal.FStar_Tactics_Types.context
              goal.FStar_Tactics_Types.goal_ty
             in
          fail1 "Not a trivial goal: %s" uu____1484))
  
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
          let uu____1501 =
            let uu____1502 = FStar_TypeChecker_Rel.simplify_guard e g  in
            uu____1502.FStar_TypeChecker_Env.guard_f  in
          match uu____1501 with
          | FStar_TypeChecker_Common.Trivial  -> ret ()
          | FStar_TypeChecker_Common.NonTrivial f ->
              let uu____1506 = istrivial e f  in
              if uu____1506
              then ret ()
              else
                (let uu____1510 = mk_irrelevant_goal reason e f opts  in
                 bind uu____1510
                   (fun goal  ->
                      let goal1 =
                        let uu___73_1517 = goal  in
                        {
                          FStar_Tactics_Types.context =
                            (uu___73_1517.FStar_Tactics_Types.context);
                          FStar_Tactics_Types.witness =
                            (uu___73_1517.FStar_Tactics_Types.witness);
                          FStar_Tactics_Types.goal_ty =
                            (uu___73_1517.FStar_Tactics_Types.goal_ty);
                          FStar_Tactics_Types.opts =
                            (uu___73_1517.FStar_Tactics_Types.opts);
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
          let uu____1538 =
            let uu____1539 = FStar_TypeChecker_Rel.simplify_guard e g  in
            uu____1539.FStar_TypeChecker_Env.guard_f  in
          match uu____1538 with
          | FStar_TypeChecker_Common.Trivial  ->
              ret FStar_Pervasives_Native.None
          | FStar_TypeChecker_Common.NonTrivial f ->
              let uu____1547 = istrivial e f  in
              if uu____1547
              then ret FStar_Pervasives_Native.None
              else
                (let uu____1555 = mk_irrelevant_goal reason e f opts  in
                 bind uu____1555
                   (fun goal  ->
                      ret
                        (FStar_Pervasives_Native.Some
                           (let uu___74_1565 = goal  in
                            {
                              FStar_Tactics_Types.context =
                                (uu___74_1565.FStar_Tactics_Types.context);
                              FStar_Tactics_Types.witness =
                                (uu___74_1565.FStar_Tactics_Types.witness);
                              FStar_Tactics_Types.goal_ty =
                                (uu___74_1565.FStar_Tactics_Types.goal_ty);
                              FStar_Tactics_Types.opts =
                                (uu___74_1565.FStar_Tactics_Types.opts);
                              FStar_Tactics_Types.is_guard = true
                            }))))
  
let (smt : Prims.unit tac) =
  bind cur_goal
    (fun g  ->
       let uu____1573 = is_irrelevant g  in
       if uu____1573
       then bind dismiss (fun uu____1577  -> add_smt_goals [g])
       else
         (let uu____1579 =
            tts g.FStar_Tactics_Types.context g.FStar_Tactics_Types.goal_ty
             in
          fail1 "goal is not irrelevant: cannot dispatch to smt (%s)"
            uu____1579))
  
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
             let uu____1620 =
               try
                 let uu____1654 =
                   let uu____1663 = FStar_BigInt.to_int_fs n1  in
                   FStar_List.splitAt uu____1663 p.FStar_Tactics_Types.goals
                    in
                 ret uu____1654
               with | uu____1685 -> fail "divide: not enough goals"  in
             bind uu____1620
               (fun uu____1712  ->
                  match uu____1712 with
                  | (lgs,rgs) ->
                      let lp =
                        let uu___75_1738 = p  in
                        {
                          FStar_Tactics_Types.main_context =
                            (uu___75_1738.FStar_Tactics_Types.main_context);
                          FStar_Tactics_Types.main_goal =
                            (uu___75_1738.FStar_Tactics_Types.main_goal);
                          FStar_Tactics_Types.all_implicits =
                            (uu___75_1738.FStar_Tactics_Types.all_implicits);
                          FStar_Tactics_Types.goals = lgs;
                          FStar_Tactics_Types.smt_goals = [];
                          FStar_Tactics_Types.depth =
                            (uu___75_1738.FStar_Tactics_Types.depth);
                          FStar_Tactics_Types.__dump =
                            (uu___75_1738.FStar_Tactics_Types.__dump);
                          FStar_Tactics_Types.psc =
                            (uu___75_1738.FStar_Tactics_Types.psc);
                          FStar_Tactics_Types.entry_range =
                            (uu___75_1738.FStar_Tactics_Types.entry_range)
                        }  in
                      let rp =
                        let uu___76_1740 = p  in
                        {
                          FStar_Tactics_Types.main_context =
                            (uu___76_1740.FStar_Tactics_Types.main_context);
                          FStar_Tactics_Types.main_goal =
                            (uu___76_1740.FStar_Tactics_Types.main_goal);
                          FStar_Tactics_Types.all_implicits =
                            (uu___76_1740.FStar_Tactics_Types.all_implicits);
                          FStar_Tactics_Types.goals = rgs;
                          FStar_Tactics_Types.smt_goals = [];
                          FStar_Tactics_Types.depth =
                            (uu___76_1740.FStar_Tactics_Types.depth);
                          FStar_Tactics_Types.__dump =
                            (uu___76_1740.FStar_Tactics_Types.__dump);
                          FStar_Tactics_Types.psc =
                            (uu___76_1740.FStar_Tactics_Types.psc);
                          FStar_Tactics_Types.entry_range =
                            (uu___76_1740.FStar_Tactics_Types.entry_range)
                        }  in
                      let uu____1741 = set lp  in
                      bind uu____1741
                        (fun uu____1749  ->
                           bind l
                             (fun a  ->
                                bind get
                                  (fun lp'  ->
                                     let uu____1763 = set rp  in
                                     bind uu____1763
                                       (fun uu____1771  ->
                                          bind r
                                            (fun b  ->
                                               bind get
                                                 (fun rp'  ->
                                                    let p' =
                                                      let uu___77_1787 = p
                                                         in
                                                      {
                                                        FStar_Tactics_Types.main_context
                                                          =
                                                          (uu___77_1787.FStar_Tactics_Types.main_context);
                                                        FStar_Tactics_Types.main_goal
                                                          =
                                                          (uu___77_1787.FStar_Tactics_Types.main_goal);
                                                        FStar_Tactics_Types.all_implicits
                                                          =
                                                          (uu___77_1787.FStar_Tactics_Types.all_implicits);
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
                                                          (uu___77_1787.FStar_Tactics_Types.depth);
                                                        FStar_Tactics_Types.__dump
                                                          =
                                                          (uu___77_1787.FStar_Tactics_Types.__dump);
                                                        FStar_Tactics_Types.psc
                                                          =
                                                          (uu___77_1787.FStar_Tactics_Types.psc);
                                                        FStar_Tactics_Types.entry_range
                                                          =
                                                          (uu___77_1787.FStar_Tactics_Types.entry_range)
                                                      }  in
                                                    let uu____1788 = set p'
                                                       in
                                                    bind uu____1788
                                                      (fun uu____1796  ->
                                                         ret (a, b))))))))))
  
let focus : 'a . 'a tac -> 'a tac =
  fun f  ->
    let uu____1814 = divide FStar_BigInt.one f idtac  in
    bind uu____1814
      (fun uu____1827  -> match uu____1827 with | (a,()) -> ret a)
  
let rec map : 'a . 'a tac -> 'a Prims.list tac =
  fun tau  ->
    bind get
      (fun p  ->
         match p.FStar_Tactics_Types.goals with
         | [] -> ret []
         | uu____1861::uu____1862 ->
             let uu____1865 =
               let uu____1874 = map tau  in
               divide FStar_BigInt.one tau uu____1874  in
             bind uu____1865
               (fun uu____1892  ->
                  match uu____1892 with | (h,t) -> ret (h :: t)))
  
let (seq : Prims.unit tac -> Prims.unit tac -> Prims.unit tac) =
  fun t1  ->
    fun t2  ->
      let uu____1929 =
        bind t1
          (fun uu____1934  ->
             let uu____1935 = map t2  in
             bind uu____1935 (fun uu____1943  -> ret ()))
         in
      focus uu____1929
  
let (intro : FStar_Syntax_Syntax.binder tac) =
  bind cur_goal
    (fun goal  ->
       let uu____1956 =
         FStar_Syntax_Util.arrow_one goal.FStar_Tactics_Types.goal_ty  in
       match uu____1956 with
       | FStar_Pervasives_Native.Some (b,c) ->
           let uu____1971 =
             let uu____1972 = FStar_Syntax_Util.is_total_comp c  in
             Prims.op_Negation uu____1972  in
           if uu____1971
           then fail "Codomain is effectful"
           else
             (let env' =
                FStar_TypeChecker_Env.push_binders
                  goal.FStar_Tactics_Types.context [b]
                 in
              let typ' = comp_to_typ c  in
              let uu____1978 = new_uvar "intro" env' typ'  in
              bind uu____1978
                (fun u  ->
                   let uu____1985 =
                     let uu____1986 =
                       FStar_Syntax_Util.abs [b] u
                         FStar_Pervasives_Native.None
                        in
                     trysolve goal uu____1986  in
                   if uu____1985
                   then
                     let uu____1989 =
                       let uu____1992 =
                         let uu___80_1993 = goal  in
                         let uu____1994 = bnorm env' u  in
                         let uu____1995 = bnorm env' typ'  in
                         {
                           FStar_Tactics_Types.context = env';
                           FStar_Tactics_Types.witness = uu____1994;
                           FStar_Tactics_Types.goal_ty = uu____1995;
                           FStar_Tactics_Types.opts =
                             (uu___80_1993.FStar_Tactics_Types.opts);
                           FStar_Tactics_Types.is_guard =
                             (uu___80_1993.FStar_Tactics_Types.is_guard)
                         }  in
                       replace_cur uu____1992  in
                     bind uu____1989 (fun uu____1997  -> ret b)
                   else fail "intro: unification failed"))
       | FStar_Pervasives_Native.None  ->
           let uu____2003 =
             tts goal.FStar_Tactics_Types.context
               goal.FStar_Tactics_Types.goal_ty
              in
           fail1 "intro: goal is not an arrow (%s)" uu____2003)
  
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
       (let uu____2030 =
          FStar_Syntax_Util.arrow_one goal.FStar_Tactics_Types.goal_ty  in
        match uu____2030 with
        | FStar_Pervasives_Native.Some (b,c) ->
            let uu____2049 =
              let uu____2050 = FStar_Syntax_Util.is_total_comp c  in
              Prims.op_Negation uu____2050  in
            if uu____2049
            then fail "Codomain is effectful"
            else
              (let bv =
                 FStar_Syntax_Syntax.gen_bv "__recf"
                   FStar_Pervasives_Native.None
                   goal.FStar_Tactics_Types.goal_ty
                  in
               let bs =
                 let uu____2066 = FStar_Syntax_Syntax.mk_binder bv  in
                 [uu____2066; b]  in
               let env' =
                 FStar_TypeChecker_Env.push_binders
                   goal.FStar_Tactics_Types.context bs
                  in
               let uu____2068 =
                 let uu____2071 = comp_to_typ c  in
                 new_uvar "intro_rec" env' uu____2071  in
               bind uu____2068
                 (fun u  ->
                    let lb =
                      let uu____2087 =
                        FStar_Syntax_Util.abs [b] u
                          FStar_Pervasives_Native.None
                         in
                      FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl bv) []
                        goal.FStar_Tactics_Types.goal_ty
                        FStar_Parser_Const.effect_Tot_lid uu____2087
                       in
                    let body = FStar_Syntax_Syntax.bv_to_name bv  in
                    let uu____2091 =
                      FStar_Syntax_Subst.close_let_rec [lb] body  in
                    match uu____2091 with
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
                          let uu____2128 =
                            let uu____2131 =
                              let uu___81_2132 = goal  in
                              let uu____2133 = bnorm env' u  in
                              let uu____2134 =
                                let uu____2135 = comp_to_typ c  in
                                bnorm env' uu____2135  in
                              {
                                FStar_Tactics_Types.context = env';
                                FStar_Tactics_Types.witness = uu____2133;
                                FStar_Tactics_Types.goal_ty = uu____2134;
                                FStar_Tactics_Types.opts =
                                  (uu___81_2132.FStar_Tactics_Types.opts);
                                FStar_Tactics_Types.is_guard =
                                  (uu___81_2132.FStar_Tactics_Types.is_guard)
                              }  in
                            replace_cur uu____2131  in
                          bind uu____2128
                            (fun uu____2142  ->
                               let uu____2143 =
                                 let uu____2148 =
                                   FStar_Syntax_Syntax.mk_binder bv  in
                                 (uu____2148, b)  in
                               ret uu____2143)
                        else fail "intro_rec: unification failed"))
        | FStar_Pervasives_Native.None  ->
            let uu____2162 =
              tts goal.FStar_Tactics_Types.context
                goal.FStar_Tactics_Types.goal_ty
               in
            fail1 "intro_rec: goal is not an arrow (%s)" uu____2162))
  
let (norm : FStar_Syntax_Embeddings.norm_step Prims.list -> Prims.unit tac) =
  fun s  ->
    bind cur_goal
      (fun goal  ->
         let steps =
           let uu____2186 = FStar_TypeChecker_Normalize.tr_norm_steps s  in
           FStar_List.append
             [FStar_TypeChecker_Normalize.Reify;
             FStar_TypeChecker_Normalize.UnfoldTac] uu____2186
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
           (let uu___82_2193 = goal  in
            {
              FStar_Tactics_Types.context =
                (uu___82_2193.FStar_Tactics_Types.context);
              FStar_Tactics_Types.witness = w;
              FStar_Tactics_Types.goal_ty = t;
              FStar_Tactics_Types.opts =
                (uu___82_2193.FStar_Tactics_Types.opts);
              FStar_Tactics_Types.is_guard =
                (uu___82_2193.FStar_Tactics_Types.is_guard)
            }))
  
let (norm_term_env :
  env ->
    FStar_Syntax_Embeddings.norm_step Prims.list ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac)
  =
  fun e  ->
    fun s  ->
      fun t  ->
        let uu____2211 =
          bind get
            (fun ps  ->
               let uu____2217 = __tc e t  in
               bind uu____2217
                 (fun uu____2239  ->
                    match uu____2239 with
                    | (t1,uu____2249,guard) ->
                        (FStar_TypeChecker_Rel.force_trivial_guard e guard;
                         (let steps =
                            let uu____2255 =
                              FStar_TypeChecker_Normalize.tr_norm_steps s  in
                            FStar_List.append
                              [FStar_TypeChecker_Normalize.Reify;
                              FStar_TypeChecker_Normalize.UnfoldTac]
                              uu____2255
                             in
                          let t2 =
                            normalize steps
                              ps.FStar_Tactics_Types.main_context t1
                             in
                          ret t2))))
           in
        FStar_All.pipe_left (wrap_err "norm_term") uu____2211
  
let (refine_intro : Prims.unit tac) =
  let uu____2267 =
    bind cur_goal
      (fun g  ->
         let uu____2274 =
           FStar_TypeChecker_Rel.base_and_refinement
             g.FStar_Tactics_Types.context g.FStar_Tactics_Types.goal_ty
            in
         match uu____2274 with
         | (uu____2287,FStar_Pervasives_Native.None ) ->
             fail "not a refinement"
         | (t,FStar_Pervasives_Native.Some (bv,phi)) ->
             let g1 =
               let uu___83_2312 = g  in
               {
                 FStar_Tactics_Types.context =
                   (uu___83_2312.FStar_Tactics_Types.context);
                 FStar_Tactics_Types.witness =
                   (uu___83_2312.FStar_Tactics_Types.witness);
                 FStar_Tactics_Types.goal_ty = t;
                 FStar_Tactics_Types.opts =
                   (uu___83_2312.FStar_Tactics_Types.opts);
                 FStar_Tactics_Types.is_guard =
                   (uu___83_2312.FStar_Tactics_Types.is_guard)
               }  in
             let uu____2313 =
               let uu____2318 =
                 let uu____2323 =
                   let uu____2324 = FStar_Syntax_Syntax.mk_binder bv  in
                   [uu____2324]  in
                 FStar_Syntax_Subst.open_term uu____2323 phi  in
               match uu____2318 with
               | (bvs,phi1) ->
                   let uu____2331 =
                     let uu____2332 = FStar_List.hd bvs  in
                     FStar_Pervasives_Native.fst uu____2332  in
                   (uu____2331, phi1)
                in
             (match uu____2313 with
              | (bv1,phi1) ->
                  let uu____2345 =
                    let uu____2348 =
                      FStar_Syntax_Subst.subst
                        [FStar_Syntax_Syntax.NT
                           (bv1, (g.FStar_Tactics_Types.witness))] phi1
                       in
                    mk_irrelevant_goal "refine_intro refinement"
                      g.FStar_Tactics_Types.context uu____2348
                      g.FStar_Tactics_Types.opts
                     in
                  bind uu____2345
                    (fun g2  ->
                       bind dismiss (fun uu____2352  -> add_goals [g1; g2]))))
     in
  FStar_All.pipe_left (wrap_err "refine_intro") uu____2267 
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
             let uu____2376 = __tc env t  in
             bind uu____2376
               (fun uu____2396  ->
                  match uu____2396 with
                  | (t1,typ,guard) ->
                      let uu____2408 =
                        if force_guard
                        then
                          must_trivial goal.FStar_Tactics_Types.context guard
                        else
                          add_goal_from_guard "__exact typing"
                            goal.FStar_Tactics_Types.context guard
                            goal.FStar_Tactics_Types.opts
                         in
                      bind uu____2408
                        (fun uu____2415  ->
                           mlog
                             (fun uu____2419  ->
                                let uu____2420 =
                                  tts goal.FStar_Tactics_Types.context typ
                                   in
                                let uu____2421 =
                                  tts goal.FStar_Tactics_Types.context
                                    goal.FStar_Tactics_Types.goal_ty
                                   in
                                FStar_Util.print2
                                  "exact: unifying %s and %s\n" uu____2420
                                  uu____2421)
                             (fun uu____2424  ->
                                let uu____2425 =
                                  do_unify goal.FStar_Tactics_Types.context
                                    typ goal.FStar_Tactics_Types.goal_ty
                                   in
                                if uu____2425
                                then solve goal t1
                                else
                                  (let uu____2429 =
                                     tts goal.FStar_Tactics_Types.context t1
                                      in
                                   let uu____2430 =
                                     tts goal.FStar_Tactics_Types.context typ
                                      in
                                   let uu____2431 =
                                     tts goal.FStar_Tactics_Types.context
                                       goal.FStar_Tactics_Types.goal_ty
                                      in
                                   fail3
                                     "%s : %s does not exactly solve the goal %s"
                                     uu____2429 uu____2430 uu____2431)))))
  
let (t_exact :
  Prims.bool -> Prims.bool -> FStar_Syntax_Syntax.term -> Prims.unit tac) =
  fun set_expected_typ1  ->
    fun force_guard  ->
      fun tm  ->
        let uu____2445 =
          mlog
            (fun uu____2450  ->
               let uu____2451 = FStar_Syntax_Print.term_to_string tm  in
               FStar_Util.print1 "exact: tm = %s\n" uu____2451)
            (fun uu____2454  ->
               let uu____2455 =
                 let uu____2462 =
                   __exact_now set_expected_typ1 force_guard tm  in
                 trytac' uu____2462  in
               bind uu____2455
                 (fun uu___57_2471  ->
                    match uu___57_2471 with
                    | FStar_Util.Inr r -> ret ()
                    | FStar_Util.Inl e ->
                        let uu____2480 =
                          let uu____2487 =
                            let uu____2490 =
                              norm [FStar_Syntax_Embeddings.Delta]  in
                            bind uu____2490
                              (fun uu____2494  ->
                                 bind refine_intro
                                   (fun uu____2496  ->
                                      __exact_now set_expected_typ1
                                        force_guard tm))
                             in
                          trytac' uu____2487  in
                        bind uu____2480
                          (fun uu___56_2503  ->
                             match uu___56_2503 with
                             | FStar_Util.Inr r -> ret ()
                             | FStar_Util.Inl uu____2511 -> fail e)))
           in
        FStar_All.pipe_left (wrap_err "exact") uu____2445
  
let (uvar_free_in_goal :
  FStar_Syntax_Syntax.uvar -> FStar_Tactics_Types.goal -> Prims.bool) =
  fun u  ->
    fun g  ->
      if g.FStar_Tactics_Types.is_guard
      then false
      else
        (let free_uvars =
           let uu____2526 =
             let uu____2533 =
               FStar_Syntax_Free.uvars g.FStar_Tactics_Types.goal_ty  in
             FStar_Util.set_elements uu____2533  in
           FStar_List.map FStar_Pervasives_Native.fst uu____2526  in
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
          let uu____2593 = f x  in
          bind uu____2593
            (fun y  ->
               let uu____2601 = mapM f xs  in
               bind uu____2601 (fun ys  -> ret (y :: ys)))
  
exception NoUnif 
let (uu___is_NoUnif : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with | NoUnif  -> true | uu____2619 -> false
  
let rec (__apply :
  Prims.bool ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.typ -> Prims.unit tac)
  =
  fun uopt  ->
    fun tm  ->
      fun typ  ->
        bind cur_goal
          (fun goal  ->
             let uu____2636 =
               let uu____2641 = t_exact false true tm  in trytac uu____2641
                in
             bind uu____2636
               (fun uu___58_2648  ->
                  match uu___58_2648 with
                  | FStar_Pervasives_Native.Some r -> ret ()
                  | FStar_Pervasives_Native.None  ->
                      let uu____2654 = FStar_Syntax_Util.arrow_one typ  in
                      (match uu____2654 with
                       | FStar_Pervasives_Native.None  ->
                           FStar_Exn.raise NoUnif
                       | FStar_Pervasives_Native.Some ((bv,aq),c) ->
                           mlog
                             (fun uu____2686  ->
                                let uu____2687 =
                                  FStar_Syntax_Print.binder_to_string
                                    (bv, aq)
                                   in
                                FStar_Util.print1
                                  "__apply: pushing binder %s\n" uu____2687)
                             (fun uu____2690  ->
                                let uu____2691 =
                                  let uu____2692 =
                                    FStar_Syntax_Util.is_total_comp c  in
                                  Prims.op_Negation uu____2692  in
                                if uu____2691
                                then fail "apply: not total codomain"
                                else
                                  (let uu____2696 =
                                     new_uvar "apply"
                                       goal.FStar_Tactics_Types.context
                                       bv.FStar_Syntax_Syntax.sort
                                      in
                                   bind uu____2696
                                     (fun u  ->
                                        let tm' =
                                          FStar_Syntax_Syntax.mk_Tm_app tm
                                            [(u, aq)]
                                            FStar_Pervasives_Native.None
                                            (goal.FStar_Tactics_Types.context).FStar_TypeChecker_Env.range
                                           in
                                        let typ' =
                                          let uu____2716 = comp_to_typ c  in
                                          FStar_All.pipe_left
                                            (FStar_Syntax_Subst.subst
                                               [FStar_Syntax_Syntax.NT
                                                  (bv, u)]) uu____2716
                                           in
                                        let uu____2717 =
                                          __apply uopt tm' typ'  in
                                        bind uu____2717
                                          (fun uu____2725  ->
                                             let u1 =
                                               bnorm
                                                 goal.FStar_Tactics_Types.context
                                                 u
                                                in
                                             let uu____2727 =
                                               let uu____2728 =
                                                 let uu____2731 =
                                                   let uu____2732 =
                                                     FStar_Syntax_Util.head_and_args
                                                       u1
                                                      in
                                                   FStar_Pervasives_Native.fst
                                                     uu____2732
                                                    in
                                                 FStar_Syntax_Subst.compress
                                                   uu____2731
                                                  in
                                               uu____2728.FStar_Syntax_Syntax.n
                                                in
                                             match uu____2727 with
                                             | FStar_Syntax_Syntax.Tm_uvar
                                                 (uvar,uu____2760) ->
                                                 bind get
                                                   (fun ps  ->
                                                      let uu____2788 =
                                                        uopt &&
                                                          (uvar_free uvar ps)
                                                         in
                                                      if uu____2788
                                                      then ret ()
                                                      else
                                                        (let uu____2792 =
                                                           let uu____2795 =
                                                             let uu___84_2796
                                                               = goal  in
                                                             let uu____2797 =
                                                               bnorm
                                                                 goal.FStar_Tactics_Types.context
                                                                 u1
                                                                in
                                                             let uu____2798 =
                                                               bnorm
                                                                 goal.FStar_Tactics_Types.context
                                                                 bv.FStar_Syntax_Syntax.sort
                                                                in
                                                             {
                                                               FStar_Tactics_Types.context
                                                                 =
                                                                 (uu___84_2796.FStar_Tactics_Types.context);
                                                               FStar_Tactics_Types.witness
                                                                 = uu____2797;
                                                               FStar_Tactics_Types.goal_ty
                                                                 = uu____2798;
                                                               FStar_Tactics_Types.opts
                                                                 =
                                                                 (uu___84_2796.FStar_Tactics_Types.opts);
                                                               FStar_Tactics_Types.is_guard
                                                                 = false
                                                             }  in
                                                           [uu____2795]  in
                                                         add_goals uu____2792))
                                             | t -> ret ())))))))
  
let try_unif : 'a . 'a tac -> 'a tac -> 'a tac =
  fun t  ->
    fun t'  -> mk_tac (fun ps  -> try run t ps with | NoUnif  -> run t' ps)
  
let (apply : Prims.bool -> FStar_Syntax_Syntax.term -> Prims.unit tac) =
  fun uopt  ->
    fun tm  ->
      let uu____2844 =
        mlog
          (fun uu____2849  ->
             let uu____2850 = FStar_Syntax_Print.term_to_string tm  in
             FStar_Util.print1 "apply: tm = %s\n" uu____2850)
          (fun uu____2852  ->
             bind cur_goal
               (fun goal  ->
                  let uu____2856 = __tc goal.FStar_Tactics_Types.context tm
                     in
                  bind uu____2856
                    (fun uu____2877  ->
                       match uu____2877 with
                       | (tm1,typ,guard) ->
                           let uu____2889 =
                             let uu____2892 =
                               let uu____2895 = __apply uopt tm1 typ  in
                               bind uu____2895
                                 (fun uu____2899  ->
                                    add_goal_from_guard "apply guard"
                                      goal.FStar_Tactics_Types.context guard
                                      goal.FStar_Tactics_Types.opts)
                                in
                             focus uu____2892  in
                           let uu____2900 =
                             let uu____2903 =
                               tts goal.FStar_Tactics_Types.context tm1  in
                             let uu____2904 =
                               tts goal.FStar_Tactics_Types.context typ  in
                             let uu____2905 =
                               tts goal.FStar_Tactics_Types.context
                                 goal.FStar_Tactics_Types.goal_ty
                                in
                             fail3
                               "Cannot instantiate %s (of type %s) to match goal (%s)"
                               uu____2903 uu____2904 uu____2905
                              in
                           try_unif uu____2889 uu____2900)))
         in
      FStar_All.pipe_left (wrap_err "apply") uu____2844
  
let (apply_lemma : FStar_Syntax_Syntax.term -> Prims.unit tac) =
  fun tm  ->
    let uu____2917 =
      let uu____2920 =
        mlog
          (fun uu____2925  ->
             let uu____2926 = FStar_Syntax_Print.term_to_string tm  in
             FStar_Util.print1 "apply_lemma: tm = %s\n" uu____2926)
          (fun uu____2929  ->
             let is_unit_t t =
               let uu____2934 =
                 let uu____2935 = FStar_Syntax_Subst.compress t  in
                 uu____2935.FStar_Syntax_Syntax.n  in
               match uu____2934 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.unit_lid
                   -> true
               | uu____2939 -> false  in
             bind cur_goal
               (fun goal  ->
                  let uu____2943 = __tc goal.FStar_Tactics_Types.context tm
                     in
                  bind uu____2943
                    (fun uu____2965  ->
                       match uu____2965 with
                       | (tm1,t,guard) ->
                           let uu____2977 =
                             FStar_Syntax_Util.arrow_formals_comp t  in
                           (match uu____2977 with
                            | (bs,comp) ->
                                if
                                  Prims.op_Negation
                                    (FStar_Syntax_Util.is_lemma_comp comp)
                                then fail "not a lemma"
                                else
                                  (let uu____3007 =
                                     FStar_List.fold_left
                                       (fun uu____3053  ->
                                          fun uu____3054  ->
                                            match (uu____3053, uu____3054)
                                            with
                                            | ((uvs,guard1,subst1),(b,aq)) ->
                                                let b_t =
                                                  FStar_Syntax_Subst.subst
                                                    subst1
                                                    b.FStar_Syntax_Syntax.sort
                                                   in
                                                let uu____3157 =
                                                  is_unit_t b_t  in
                                                if uu____3157
                                                then
                                                  (((FStar_Syntax_Util.exp_unit,
                                                      aq) :: uvs), guard1,
                                                    ((FStar_Syntax_Syntax.NT
                                                        (b,
                                                          FStar_Syntax_Util.exp_unit))
                                                    :: subst1))
                                                else
                                                  (let uu____3195 =
                                                     FStar_TypeChecker_Util.new_implicit_var
                                                       "apply_lemma"
                                                       (goal.FStar_Tactics_Types.goal_ty).FStar_Syntax_Syntax.pos
                                                       goal.FStar_Tactics_Types.context
                                                       b_t
                                                      in
                                                   match uu____3195 with
                                                   | (u,uu____3225,g_u) ->
                                                       let uu____3239 =
                                                         FStar_TypeChecker_Rel.conj_guard
                                                           guard1 g_u
                                                          in
                                                       (((u, aq) :: uvs),
                                                         uu____3239,
                                                         ((FStar_Syntax_Syntax.NT
                                                             (b, u)) ::
                                                         subst1))))
                                       ([], guard, []) bs
                                      in
                                   match uu____3007 with
                                   | (uvs,implicits,subst1) ->
                                       let uvs1 = FStar_List.rev uvs  in
                                       let comp1 =
                                         FStar_Syntax_Subst.subst_comp subst1
                                           comp
                                          in
                                       let uu____3309 =
                                         let uu____3318 =
                                           let uu____3327 =
                                             FStar_Syntax_Util.comp_to_comp_typ
                                               comp1
                                              in
                                           uu____3327.FStar_Syntax_Syntax.effect_args
                                            in
                                         match uu____3318 with
                                         | pre::post::uu____3338 ->
                                             ((FStar_Pervasives_Native.fst
                                                 pre),
                                               (FStar_Pervasives_Native.fst
                                                  post))
                                         | uu____3379 ->
                                             failwith
                                               "apply_lemma: impossible: not a lemma"
                                          in
                                       (match uu____3309 with
                                        | (pre,post) ->
                                            let post1 =
                                              let uu____3411 =
                                                let uu____3420 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    FStar_Syntax_Util.exp_unit
                                                   in
                                                [uu____3420]  in
                                              FStar_Syntax_Util.mk_app post
                                                uu____3411
                                               in
                                            let uu____3421 =
                                              let uu____3422 =
                                                let uu____3423 =
                                                  FStar_Syntax_Util.mk_squash
                                                    FStar_Syntax_Syntax.U_zero
                                                    post1
                                                   in
                                                do_unify
                                                  goal.FStar_Tactics_Types.context
                                                  uu____3423
                                                  goal.FStar_Tactics_Types.goal_ty
                                                 in
                                              Prims.op_Negation uu____3422
                                               in
                                            if uu____3421
                                            then
                                              let uu____3426 =
                                                tts
                                                  goal.FStar_Tactics_Types.context
                                                  tm1
                                                 in
                                              let uu____3427 =
                                                let uu____3428 =
                                                  FStar_Syntax_Util.mk_squash
                                                    FStar_Syntax_Syntax.U_zero
                                                    post1
                                                   in
                                                tts
                                                  goal.FStar_Tactics_Types.context
                                                  uu____3428
                                                 in
                                              let uu____3429 =
                                                tts
                                                  goal.FStar_Tactics_Types.context
                                                  goal.FStar_Tactics_Types.goal_ty
                                                 in
                                              fail3
                                                "Cannot instantiate lemma %s (with postcondition: %s) to match goal (%s)"
                                                uu____3426 uu____3427
                                                uu____3429
                                            else
                                              (let solution =
                                                 let uu____3432 =
                                                   FStar_Syntax_Syntax.mk_Tm_app
                                                     tm1 uvs1
                                                     FStar_Pervasives_Native.None
                                                     (goal.FStar_Tactics_Types.context).FStar_TypeChecker_Env.range
                                                    in
                                                 FStar_TypeChecker_Normalize.normalize
                                                   [FStar_TypeChecker_Normalize.Beta]
                                                   goal.FStar_Tactics_Types.context
                                                   uu____3432
                                                  in
                                               let uu____3433 =
                                                 add_implicits
                                                   implicits.FStar_TypeChecker_Env.implicits
                                                  in
                                               bind uu____3433
                                                 (fun uu____3438  ->
                                                    let uu____3439 =
                                                      solve goal
                                                        FStar_Syntax_Util.exp_unit
                                                       in
                                                    bind uu____3439
                                                      (fun uu____3447  ->
                                                         let is_free_uvar uv
                                                           t1 =
                                                           let free_uvars =
                                                             let uu____3458 =
                                                               let uu____3465
                                                                 =
                                                                 FStar_Syntax_Free.uvars
                                                                   t1
                                                                  in
                                                               FStar_Util.set_elements
                                                                 uu____3465
                                                                in
                                                             FStar_List.map
                                                               FStar_Pervasives_Native.fst
                                                               uu____3458
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
                                                           let uu____3506 =
                                                             FStar_Syntax_Util.head_and_args
                                                               t1
                                                              in
                                                           match uu____3506
                                                           with
                                                           | (hd1,uu____3522)
                                                               ->
                                                               (match 
                                                                  hd1.FStar_Syntax_Syntax.n
                                                                with
                                                                | FStar_Syntax_Syntax.Tm_uvar
                                                                    (uv,uu____3544)
                                                                    ->
                                                                    appears
                                                                    uv goals
                                                                | uu____3569
                                                                    -> false)
                                                            in
                                                         let uu____3570 =
                                                           FStar_All.pipe_right
                                                             implicits.FStar_TypeChecker_Env.implicits
                                                             (mapM
                                                                (fun
                                                                   uu____3642
                                                                    ->
                                                                   match uu____3642
                                                                   with
                                                                   | 
                                                                   (_msg,env,_uvar,term,typ,uu____3670)
                                                                    ->
                                                                    let uu____3671
                                                                    =
                                                                    FStar_Syntax_Util.head_and_args
                                                                    term  in
                                                                    (match uu____3671
                                                                    with
                                                                    | 
                                                                    (hd1,uu____3697)
                                                                    ->
                                                                    let uu____3718
                                                                    =
                                                                    let uu____3719
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    hd1  in
                                                                    uu____3719.FStar_Syntax_Syntax.n
                                                                     in
                                                                    (match uu____3718
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Tm_uvar
                                                                    uu____3732
                                                                    ->
                                                                    let uu____3749
                                                                    =
                                                                    let uu____3758
                                                                    =
                                                                    let uu____3761
                                                                    =
                                                                    let uu___87_3762
                                                                    = goal
                                                                     in
                                                                    let uu____3763
                                                                    =
                                                                    bnorm
                                                                    goal.FStar_Tactics_Types.context
                                                                    term  in
                                                                    let uu____3764
                                                                    =
                                                                    bnorm
                                                                    goal.FStar_Tactics_Types.context
                                                                    typ  in
                                                                    {
                                                                    FStar_Tactics_Types.context
                                                                    =
                                                                    (uu___87_3762.FStar_Tactics_Types.context);
                                                                    FStar_Tactics_Types.witness
                                                                    =
                                                                    uu____3763;
                                                                    FStar_Tactics_Types.goal_ty
                                                                    =
                                                                    uu____3764;
                                                                    FStar_Tactics_Types.opts
                                                                    =
                                                                    (uu___87_3762.FStar_Tactics_Types.opts);
                                                                    FStar_Tactics_Types.is_guard
                                                                    =
                                                                    (uu___87_3762.FStar_Tactics_Types.is_guard)
                                                                    }  in
                                                                    [uu____3761]
                                                                     in
                                                                    (uu____3758,
                                                                    [])  in
                                                                    ret
                                                                    uu____3749
                                                                    | 
                                                                    uu____3777
                                                                    ->
                                                                    let term1
                                                                    =
                                                                    bnorm env
                                                                    term  in
                                                                    let uu____3779
                                                                    =
                                                                    let uu____3786
                                                                    =
                                                                    FStar_TypeChecker_Env.set_expected_typ
                                                                    env typ
                                                                     in
                                                                    env.FStar_TypeChecker_Env.type_of
                                                                    uu____3786
                                                                    term1  in
                                                                    (match uu____3779
                                                                    with
                                                                    | 
                                                                    (uu____3797,uu____3798,g_typ)
                                                                    ->
                                                                    let uu____3800
                                                                    =
                                                                    goal_from_guard
                                                                    "apply_lemma solved arg"
                                                                    goal.FStar_Tactics_Types.context
                                                                    g_typ
                                                                    goal.FStar_Tactics_Types.opts
                                                                     in
                                                                    bind
                                                                    uu____3800
                                                                    (fun
                                                                    uu___59_3816
                                                                     ->
                                                                    match uu___59_3816
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
                                                                    ([], [g])))))))
                                                            in
                                                         bind uu____3570
                                                           (fun goals_  ->
                                                              let sub_goals =
                                                                let uu____3884
                                                                  =
                                                                  FStar_List.map
                                                                    FStar_Pervasives_Native.fst
                                                                    goals_
                                                                   in
                                                                FStar_List.flatten
                                                                  uu____3884
                                                                 in
                                                              let smt_goals =
                                                                let uu____3906
                                                                  =
                                                                  FStar_List.map
                                                                    FStar_Pervasives_Native.snd
                                                                    goals_
                                                                   in
                                                                FStar_List.flatten
                                                                  uu____3906
                                                                 in
                                                              let rec filter'
                                                                a f xs =
                                                                match xs with
                                                                | [] -> []
                                                                | x::xs1 ->
                                                                    let uu____3961
                                                                    = f x xs1
                                                                     in
                                                                    if
                                                                    uu____3961
                                                                    then
                                                                    let uu____3964
                                                                    =
                                                                    filter'
                                                                    () f xs1
                                                                     in x ::
                                                                    uu____3964
                                                                    else
                                                                    filter'
                                                                    () f xs1
                                                                 in
                                                              let sub_goals1
                                                                =
                                                                Obj.magic
                                                                  (filter' ()
                                                                    (fun a431
                                                                     ->
                                                                    fun a432 
                                                                    ->
                                                                    (Obj.magic
                                                                    (fun g 
                                                                    ->
                                                                    fun goals
                                                                     ->
                                                                    let uu____3978
                                                                    =
                                                                    checkone
                                                                    g.FStar_Tactics_Types.witness
                                                                    goals  in
                                                                    Prims.op_Negation
                                                                    uu____3978))
                                                                    a431 a432)
                                                                    (Obj.magic
                                                                    sub_goals))
                                                                 in
                                                              let uu____3979
                                                                =
                                                                add_goal_from_guard
                                                                  "apply_lemma guard"
                                                                  goal.FStar_Tactics_Types.context
                                                                  guard
                                                                  goal.FStar_Tactics_Types.opts
                                                                 in
                                                              bind uu____3979
                                                                (fun
                                                                   uu____3984
                                                                    ->
                                                                   let uu____3985
                                                                    =
                                                                    let uu____3988
                                                                    =
                                                                    let uu____3989
                                                                    =
                                                                    let uu____3990
                                                                    =
                                                                    FStar_Syntax_Util.mk_squash
                                                                    FStar_Syntax_Syntax.U_zero
                                                                    pre  in
                                                                    istrivial
                                                                    goal.FStar_Tactics_Types.context
                                                                    uu____3990
                                                                     in
                                                                    Prims.op_Negation
                                                                    uu____3989
                                                                     in
                                                                    if
                                                                    uu____3988
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
                                                                    uu____3985
                                                                    (fun
                                                                    uu____3996
                                                                     ->
                                                                    let uu____3997
                                                                    =
                                                                    add_smt_goals
                                                                    smt_goals
                                                                     in
                                                                    bind
                                                                    uu____3997
                                                                    (fun
                                                                    uu____4001
                                                                     ->
                                                                    add_goals
                                                                    sub_goals1)))))))))))))
         in
      focus uu____2920  in
    FStar_All.pipe_left (wrap_err "apply_lemma") uu____2917
  
let (destruct_eq' :
  FStar_Syntax_Syntax.typ ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun typ  ->
    let uu____4021 = FStar_Syntax_Util.destruct_typ_as_formula typ  in
    match uu____4021 with
    | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn
        (l,uu____4031::(e1,uu____4033)::(e2,uu____4035)::[])) when
        FStar_Ident.lid_equals l FStar_Parser_Const.eq2_lid ->
        FStar_Pervasives_Native.Some (e1, e2)
    | uu____4094 -> FStar_Pervasives_Native.None
  
let (destruct_eq :
  FStar_Syntax_Syntax.typ ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun typ  ->
    let uu____4116 = destruct_eq' typ  in
    match uu____4116 with
    | FStar_Pervasives_Native.Some t -> FStar_Pervasives_Native.Some t
    | FStar_Pervasives_Native.None  ->
        let uu____4146 = FStar_Syntax_Util.un_squash typ  in
        (match uu____4146 with
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
        let uu____4202 = FStar_TypeChecker_Env.pop_bv e1  in
        match uu____4202 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (bv',e') ->
            if FStar_Syntax_Syntax.bv_eq bvar bv'
            then FStar_Pervasives_Native.Some (e', [])
            else
              (let uu____4250 = aux e'  in
               FStar_Util.map_opt uu____4250
                 (fun uu____4274  ->
                    match uu____4274 with | (e'',bvs) -> (e'', (bv' :: bvs))))
         in
      let uu____4295 = aux e  in
      FStar_Util.map_opt uu____4295
        (fun uu____4319  ->
           match uu____4319 with | (e',bvs) -> (e', (FStar_List.rev bvs)))
  
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
          let uu____4374 = split_env b1 g.FStar_Tactics_Types.context  in
          FStar_Util.map_opt uu____4374
            (fun uu____4398  ->
               match uu____4398 with
               | (e0,bvs) ->
                   let s1 bv =
                     let uu___88_4415 = bv  in
                     let uu____4416 =
                       FStar_Syntax_Subst.subst s bv.FStar_Syntax_Syntax.sort
                        in
                     {
                       FStar_Syntax_Syntax.ppname =
                         (uu___88_4415.FStar_Syntax_Syntax.ppname);
                       FStar_Syntax_Syntax.index =
                         (uu___88_4415.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort = uu____4416
                     }  in
                   let bvs1 = FStar_List.map s1 bvs  in
                   let c = push_bvs e0 (b2 :: bvs1)  in
                   let w =
                     FStar_Syntax_Subst.subst s g.FStar_Tactics_Types.witness
                      in
                   let t =
                     FStar_Syntax_Subst.subst s g.FStar_Tactics_Types.goal_ty
                      in
                   let uu___89_4425 = g  in
                   {
                     FStar_Tactics_Types.context = c;
                     FStar_Tactics_Types.witness = w;
                     FStar_Tactics_Types.goal_ty = t;
                     FStar_Tactics_Types.opts =
                       (uu___89_4425.FStar_Tactics_Types.opts);
                     FStar_Tactics_Types.is_guard =
                       (uu___89_4425.FStar_Tactics_Types.is_guard)
                   })
  
let (rewrite : FStar_Syntax_Syntax.binder -> Prims.unit tac) =
  fun h  ->
    bind cur_goal
      (fun goal  ->
         let uu____4438 = h  in
         match uu____4438 with
         | (bv,uu____4442) ->
             mlog
               (fun uu____4446  ->
                  let uu____4447 = FStar_Syntax_Print.bv_to_string bv  in
                  let uu____4448 =
                    tts goal.FStar_Tactics_Types.context
                      bv.FStar_Syntax_Syntax.sort
                     in
                  FStar_Util.print2 "+++Rewrite %s : %s\n" uu____4447
                    uu____4448)
               (fun uu____4451  ->
                  let uu____4452 =
                    split_env bv goal.FStar_Tactics_Types.context  in
                  match uu____4452 with
                  | FStar_Pervasives_Native.None  ->
                      fail "rewrite: binder not found in environment"
                  | FStar_Pervasives_Native.Some (e0,bvs) ->
                      let uu____4481 =
                        destruct_eq bv.FStar_Syntax_Syntax.sort  in
                      (match uu____4481 with
                       | FStar_Pervasives_Native.Some (x,e) ->
                           let uu____4496 =
                             let uu____4497 = FStar_Syntax_Subst.compress x
                                in
                             uu____4497.FStar_Syntax_Syntax.n  in
                           (match uu____4496 with
                            | FStar_Syntax_Syntax.Tm_name x1 ->
                                let s = [FStar_Syntax_Syntax.NT (x1, e)]  in
                                let s1 bv1 =
                                  let uu___90_4510 = bv1  in
                                  let uu____4511 =
                                    FStar_Syntax_Subst.subst s
                                      bv1.FStar_Syntax_Syntax.sort
                                     in
                                  {
                                    FStar_Syntax_Syntax.ppname =
                                      (uu___90_4510.FStar_Syntax_Syntax.ppname);
                                    FStar_Syntax_Syntax.index =
                                      (uu___90_4510.FStar_Syntax_Syntax.index);
                                    FStar_Syntax_Syntax.sort = uu____4511
                                  }  in
                                let bvs1 = FStar_List.map s1 bvs  in
                                let uu____4517 =
                                  let uu___91_4518 = goal  in
                                  let uu____4519 = push_bvs e0 (bv :: bvs1)
                                     in
                                  let uu____4520 =
                                    FStar_Syntax_Subst.subst s
                                      goal.FStar_Tactics_Types.witness
                                     in
                                  let uu____4521 =
                                    FStar_Syntax_Subst.subst s
                                      goal.FStar_Tactics_Types.goal_ty
                                     in
                                  {
                                    FStar_Tactics_Types.context = uu____4519;
                                    FStar_Tactics_Types.witness = uu____4520;
                                    FStar_Tactics_Types.goal_ty = uu____4521;
                                    FStar_Tactics_Types.opts =
                                      (uu___91_4518.FStar_Tactics_Types.opts);
                                    FStar_Tactics_Types.is_guard =
                                      (uu___91_4518.FStar_Tactics_Types.is_guard)
                                  }  in
                                replace_cur uu____4517
                            | uu____4522 ->
                                fail
                                  "rewrite: Not an equality hypothesis with a variable on the LHS")
                       | uu____4523 ->
                           fail "rewrite: Not an equality hypothesis")))
  
let (rename_to :
  FStar_Syntax_Syntax.binder -> Prims.string -> Prims.unit tac) =
  fun b  ->
    fun s  ->
      bind cur_goal
        (fun goal  ->
           let uu____4548 = b  in
           match uu____4548 with
           | (bv,uu____4552) ->
               let bv' =
                 FStar_Syntax_Syntax.freshen_bv
                   (let uu___92_4556 = bv  in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (FStar_Ident.mk_ident
                           (s,
                             ((bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange)));
                      FStar_Syntax_Syntax.index =
                        (uu___92_4556.FStar_Syntax_Syntax.index);
                      FStar_Syntax_Syntax.sort =
                        (uu___92_4556.FStar_Syntax_Syntax.sort)
                    })
                  in
               let s1 =
                 let uu____4560 =
                   let uu____4561 =
                     let uu____4568 = FStar_Syntax_Syntax.bv_to_name bv'  in
                     (bv, uu____4568)  in
                   FStar_Syntax_Syntax.NT uu____4561  in
                 [uu____4560]  in
               let uu____4569 = subst_goal bv bv' s1 goal  in
               (match uu____4569 with
                | FStar_Pervasives_Native.None  ->
                    fail "rename_to: binder not found in environment"
                | FStar_Pervasives_Native.Some goal1 -> replace_cur goal1))
  
let (binder_retype : FStar_Syntax_Syntax.binder -> Prims.unit tac) =
  fun b  ->
    bind cur_goal
      (fun goal  ->
         let uu____4588 = b  in
         match uu____4588 with
         | (bv,uu____4592) ->
             let uu____4593 = split_env bv goal.FStar_Tactics_Types.context
                in
             (match uu____4593 with
              | FStar_Pervasives_Native.None  ->
                  fail "binder_retype: binder is not present in environment"
              | FStar_Pervasives_Native.Some (e0,bvs) ->
                  let uu____4622 = FStar_Syntax_Util.type_u ()  in
                  (match uu____4622 with
                   | (ty,u) ->
                       let uu____4631 = new_uvar "binder_retype" e0 ty  in
                       bind uu____4631
                         (fun t'  ->
                            let bv'' =
                              let uu___93_4641 = bv  in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___93_4641.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___93_4641.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = t'
                              }  in
                            let s =
                              let uu____4645 =
                                let uu____4646 =
                                  let uu____4653 =
                                    FStar_Syntax_Syntax.bv_to_name bv''  in
                                  (bv, uu____4653)  in
                                FStar_Syntax_Syntax.NT uu____4646  in
                              [uu____4645]  in
                            let bvs1 =
                              FStar_List.map
                                (fun b1  ->
                                   let uu___94_4661 = b1  in
                                   let uu____4662 =
                                     FStar_Syntax_Subst.subst s
                                       b1.FStar_Syntax_Syntax.sort
                                      in
                                   {
                                     FStar_Syntax_Syntax.ppname =
                                       (uu___94_4661.FStar_Syntax_Syntax.ppname);
                                     FStar_Syntax_Syntax.index =
                                       (uu___94_4661.FStar_Syntax_Syntax.index);
                                     FStar_Syntax_Syntax.sort = uu____4662
                                   }) bvs
                               in
                            let env' = push_bvs e0 (bv'' :: bvs1)  in
                            bind dismiss
                              (fun uu____4668  ->
                                 let uu____4669 =
                                   let uu____4672 =
                                     let uu____4675 =
                                       let uu___95_4676 = goal  in
                                       let uu____4677 =
                                         FStar_Syntax_Subst.subst s
                                           goal.FStar_Tactics_Types.witness
                                          in
                                       let uu____4678 =
                                         FStar_Syntax_Subst.subst s
                                           goal.FStar_Tactics_Types.goal_ty
                                          in
                                       {
                                         FStar_Tactics_Types.context = env';
                                         FStar_Tactics_Types.witness =
                                           uu____4677;
                                         FStar_Tactics_Types.goal_ty =
                                           uu____4678;
                                         FStar_Tactics_Types.opts =
                                           (uu___95_4676.FStar_Tactics_Types.opts);
                                         FStar_Tactics_Types.is_guard =
                                           (uu___95_4676.FStar_Tactics_Types.is_guard)
                                       }  in
                                     [uu____4675]  in
                                   add_goals uu____4672  in
                                 bind uu____4669
                                   (fun uu____4681  ->
                                      let uu____4682 =
                                        FStar_Syntax_Util.mk_eq2
                                          (FStar_Syntax_Syntax.U_succ u) ty
                                          bv.FStar_Syntax_Syntax.sort t'
                                         in
                                      add_irrelevant_goal
                                        "binder_retype equation" e0
                                        uu____4682
                                        goal.FStar_Tactics_Types.opts))))))
  
let (norm_binder_type :
  FStar_Syntax_Embeddings.norm_step Prims.list ->
    FStar_Syntax_Syntax.binder -> Prims.unit tac)
  =
  fun s  ->
    fun b  ->
      bind cur_goal
        (fun goal  ->
           let uu____4703 = b  in
           match uu____4703 with
           | (bv,uu____4707) ->
               let uu____4708 = split_env bv goal.FStar_Tactics_Types.context
                  in
               (match uu____4708 with
                | FStar_Pervasives_Native.None  ->
                    fail
                      "binder_retype: binder is not present in environment"
                | FStar_Pervasives_Native.Some (e0,bvs) ->
                    let steps =
                      let uu____4740 =
                        FStar_TypeChecker_Normalize.tr_norm_steps s  in
                      FStar_List.append
                        [FStar_TypeChecker_Normalize.Reify;
                        FStar_TypeChecker_Normalize.UnfoldTac] uu____4740
                       in
                    let sort' =
                      normalize steps e0 bv.FStar_Syntax_Syntax.sort  in
                    let bv' =
                      let uu___96_4745 = bv  in
                      {
                        FStar_Syntax_Syntax.ppname =
                          (uu___96_4745.FStar_Syntax_Syntax.ppname);
                        FStar_Syntax_Syntax.index =
                          (uu___96_4745.FStar_Syntax_Syntax.index);
                        FStar_Syntax_Syntax.sort = sort'
                      }  in
                    let env' = push_bvs e0 (bv' :: bvs)  in
                    replace_cur
                      (let uu___97_4749 = goal  in
                       {
                         FStar_Tactics_Types.context = env';
                         FStar_Tactics_Types.witness =
                           (uu___97_4749.FStar_Tactics_Types.witness);
                         FStar_Tactics_Types.goal_ty =
                           (uu___97_4749.FStar_Tactics_Types.goal_ty);
                         FStar_Tactics_Types.opts =
                           (uu___97_4749.FStar_Tactics_Types.opts);
                         FStar_Tactics_Types.is_guard =
                           (uu___97_4749.FStar_Tactics_Types.is_guard)
                       })))
  
let (revert : Prims.unit tac) =
  bind cur_goal
    (fun goal  ->
       let uu____4757 =
         FStar_TypeChecker_Env.pop_bv goal.FStar_Tactics_Types.context  in
       match uu____4757 with
       | FStar_Pervasives_Native.None  -> fail "Cannot revert; empty context"
       | FStar_Pervasives_Native.Some (x,env') ->
           let typ' =
             let uu____4779 =
               FStar_Syntax_Syntax.mk_Total goal.FStar_Tactics_Types.goal_ty
                in
             FStar_Syntax_Util.arrow [(x, FStar_Pervasives_Native.None)]
               uu____4779
              in
           let w' =
             FStar_Syntax_Util.abs [(x, FStar_Pervasives_Native.None)]
               goal.FStar_Tactics_Types.witness FStar_Pervasives_Native.None
              in
           replace_cur
             (let uu___98_4813 = goal  in
              {
                FStar_Tactics_Types.context = env';
                FStar_Tactics_Types.witness = w';
                FStar_Tactics_Types.goal_ty = typ';
                FStar_Tactics_Types.opts =
                  (uu___98_4813.FStar_Tactics_Types.opts);
                FStar_Tactics_Types.is_guard =
                  (uu___98_4813.FStar_Tactics_Types.is_guard)
              }))
  
let (free_in :
  FStar_Syntax_Syntax.bv -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun bv  ->
    fun t  ->
      let uu____4820 = FStar_Syntax_Free.names t  in
      FStar_Util.set_mem bv uu____4820
  
let rec (clear : FStar_Syntax_Syntax.binder -> Prims.unit tac) =
  fun b  ->
    let bv = FStar_Pervasives_Native.fst b  in
    bind cur_goal
      (fun goal  ->
         mlog
           (fun uu____4836  ->
              let uu____4837 = FStar_Syntax_Print.binder_to_string b  in
              let uu____4838 =
                let uu____4839 =
                  let uu____4840 =
                    FStar_TypeChecker_Env.all_binders
                      goal.FStar_Tactics_Types.context
                     in
                  FStar_All.pipe_right uu____4840 FStar_List.length  in
                FStar_All.pipe_right uu____4839 FStar_Util.string_of_int  in
              FStar_Util.print2 "Clear of (%s), env has %s binders\n"
                uu____4837 uu____4838)
           (fun uu____4851  ->
              let uu____4852 = split_env bv goal.FStar_Tactics_Types.context
                 in
              match uu____4852 with
              | FStar_Pervasives_Native.None  ->
                  fail "Cannot clear; binder not in environment"
              | FStar_Pervasives_Native.Some (e',bvs) ->
                  let rec check bvs1 =
                    match bvs1 with
                    | [] -> ret ()
                    | bv'::bvs2 ->
                        let uu____4897 =
                          free_in bv bv'.FStar_Syntax_Syntax.sort  in
                        if uu____4897
                        then
                          let uu____4900 =
                            let uu____4901 =
                              FStar_Syntax_Print.bv_to_string bv'  in
                            FStar_Util.format1
                              "Cannot clear; binder present in the type of %s"
                              uu____4901
                             in
                          fail uu____4900
                        else check bvs2
                     in
                  let uu____4903 =
                    free_in bv goal.FStar_Tactics_Types.goal_ty  in
                  if uu____4903
                  then fail "Cannot clear; binder present in goal"
                  else
                    (let uu____4907 = check bvs  in
                     bind uu____4907
                       (fun uu____4913  ->
                          let env' = push_bvs e' bvs  in
                          let uu____4915 =
                            new_uvar "clear.witness" env'
                              goal.FStar_Tactics_Types.goal_ty
                             in
                          bind uu____4915
                            (fun ut  ->
                               let uu____4921 =
                                 do_unify goal.FStar_Tactics_Types.context
                                   goal.FStar_Tactics_Types.witness ut
                                  in
                               if uu____4921
                               then
                                 replace_cur
                                   (let uu___99_4926 = goal  in
                                    {
                                      FStar_Tactics_Types.context = env';
                                      FStar_Tactics_Types.witness = ut;
                                      FStar_Tactics_Types.goal_ty =
                                        (uu___99_4926.FStar_Tactics_Types.goal_ty);
                                      FStar_Tactics_Types.opts =
                                        (uu___99_4926.FStar_Tactics_Types.opts);
                                      FStar_Tactics_Types.is_guard =
                                        (uu___99_4926.FStar_Tactics_Types.is_guard)
                                    })
                               else
                                 fail
                                   "Cannot clear; binder appears in witness")))))
  
let (clear_top : Prims.unit tac) =
  bind cur_goal
    (fun goal  ->
       let uu____4935 =
         FStar_TypeChecker_Env.pop_bv goal.FStar_Tactics_Types.context  in
       match uu____4935 with
       | FStar_Pervasives_Native.None  -> fail "Cannot clear; empty context"
       | FStar_Pervasives_Native.Some (x,uu____4949) ->
           let uu____4954 = FStar_Syntax_Syntax.mk_binder x  in
           clear uu____4954)
  
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
           let uu___100_4970 = g  in
           {
             FStar_Tactics_Types.context = ctx';
             FStar_Tactics_Types.witness =
               (uu___100_4970.FStar_Tactics_Types.witness);
             FStar_Tactics_Types.goal_ty =
               (uu___100_4970.FStar_Tactics_Types.goal_ty);
             FStar_Tactics_Types.opts =
               (uu___100_4970.FStar_Tactics_Types.opts);
             FStar_Tactics_Types.is_guard =
               (uu___100_4970.FStar_Tactics_Types.is_guard)
           }  in
         bind dismiss (fun uu____4972  -> add_goals [g']))
  
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
           let uu___101_4988 = g  in
           {
             FStar_Tactics_Types.context = ctx';
             FStar_Tactics_Types.witness =
               (uu___101_4988.FStar_Tactics_Types.witness);
             FStar_Tactics_Types.goal_ty =
               (uu___101_4988.FStar_Tactics_Types.goal_ty);
             FStar_Tactics_Types.opts =
               (uu___101_4988.FStar_Tactics_Types.opts);
             FStar_Tactics_Types.is_guard =
               (uu___101_4988.FStar_Tactics_Types.is_guard)
           }  in
         bind dismiss (fun uu____4990  -> add_goals [g']))
  
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
            let uu____5022 = FStar_Syntax_Subst.compress t  in
            uu____5022.FStar_Syntax_Syntax.n  in
          let uu____5025 =
            if d = FStar_Tactics_Types.TopDown
            then
              f env
                (let uu___103_5031 = t  in
                 {
                   FStar_Syntax_Syntax.n = tn;
                   FStar_Syntax_Syntax.pos =
                     (uu___103_5031.FStar_Syntax_Syntax.pos);
                   FStar_Syntax_Syntax.vars =
                     (uu___103_5031.FStar_Syntax_Syntax.vars)
                 })
            else ret t  in
          bind uu____5025
            (fun t1  ->
               let tn1 =
                 let uu____5039 =
                   let uu____5040 = FStar_Syntax_Subst.compress t1  in
                   uu____5040.FStar_Syntax_Syntax.n  in
                 match uu____5039 with
                 | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
                     let ff = tac_fold_env d f env  in
                     let uu____5072 = ff hd1  in
                     bind uu____5072
                       (fun hd2  ->
                          let fa uu____5092 =
                            match uu____5092 with
                            | (a,q) ->
                                let uu____5105 = ff a  in
                                bind uu____5105 (fun a1  -> ret (a1, q))
                             in
                          let uu____5118 = mapM fa args  in
                          bind uu____5118
                            (fun args1  ->
                               ret (FStar_Syntax_Syntax.Tm_app (hd2, args1))))
                 | FStar_Syntax_Syntax.Tm_abs (bs,t2,k) ->
                     let uu____5178 = FStar_Syntax_Subst.open_term bs t2  in
                     (match uu____5178 with
                      | (bs1,t') ->
                          let uu____5187 =
                            let uu____5190 =
                              FStar_TypeChecker_Env.push_binders env bs1  in
                            tac_fold_env d f uu____5190 t'  in
                          bind uu____5187
                            (fun t''  ->
                               let uu____5194 =
                                 let uu____5195 =
                                   let uu____5212 =
                                     FStar_Syntax_Subst.close_binders bs1  in
                                   let uu____5213 =
                                     FStar_Syntax_Subst.close bs1 t''  in
                                   (uu____5212, uu____5213, k)  in
                                 FStar_Syntax_Syntax.Tm_abs uu____5195  in
                               ret uu____5194))
                 | FStar_Syntax_Syntax.Tm_arrow (bs,k) -> ret tn
                 | uu____5234 -> ret tn  in
               bind tn1
                 (fun tn2  ->
                    let t' =
                      let uu___102_5241 = t1  in
                      {
                        FStar_Syntax_Syntax.n = tn2;
                        FStar_Syntax_Syntax.pos =
                          (uu___102_5241.FStar_Syntax_Syntax.pos);
                        FStar_Syntax_Syntax.vars =
                          (uu___102_5241.FStar_Syntax_Syntax.vars)
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
            let uu____5270 = FStar_TypeChecker_TcTerm.tc_term env t  in
            match uu____5270 with
            | (t1,lcomp,g) ->
                let uu____5282 =
                  (let uu____5285 =
                     FStar_Syntax_Util.is_pure_or_ghost_lcomp lcomp  in
                   Prims.op_Negation uu____5285) ||
                    (let uu____5287 = FStar_TypeChecker_Rel.is_trivial g  in
                     Prims.op_Negation uu____5287)
                   in
                if uu____5282
                then ret t1
                else
                  (let rewrite_eq =
                     let typ = lcomp.FStar_Syntax_Syntax.res_typ  in
                     let uu____5297 = new_uvar "pointwise_rec" env typ  in
                     bind uu____5297
                       (fun ut  ->
                          log ps
                            (fun uu____5308  ->
                               let uu____5309 =
                                 FStar_Syntax_Print.term_to_string t1  in
                               let uu____5310 =
                                 FStar_Syntax_Print.term_to_string ut  in
                               FStar_Util.print2
                                 "Pointwise_rec: making equality\n\t%s ==\n\t%s\n"
                                 uu____5309 uu____5310);
                          (let uu____5311 =
                             let uu____5314 =
                               let uu____5315 =
                                 FStar_TypeChecker_TcTerm.universe_of env typ
                                  in
                               FStar_Syntax_Util.mk_eq2 uu____5315 typ t1 ut
                                in
                             add_irrelevant_goal "pointwise_rec equation" env
                               uu____5314 opts
                              in
                           bind uu____5311
                             (fun uu____5318  ->
                                let uu____5319 =
                                  bind tau
                                    (fun uu____5325  ->
                                       let ut1 =
                                         FStar_TypeChecker_Normalize.reduce_uvar_solutions
                                           env ut
                                          in
                                       log ps
                                         (fun uu____5331  ->
                                            let uu____5332 =
                                              FStar_Syntax_Print.term_to_string
                                                t1
                                               in
                                            let uu____5333 =
                                              FStar_Syntax_Print.term_to_string
                                                ut1
                                               in
                                            FStar_Util.print2
                                              "Pointwise_rec: succeeded rewriting\n\t%s to\n\t%s\n"
                                              uu____5332 uu____5333);
                                       ret ut1)
                                   in
                                focus uu____5319)))
                      in
                   let uu____5334 = trytac' rewrite_eq  in
                   bind uu____5334
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
           let uu____5376 =
             match ps.FStar_Tactics_Types.goals with
             | g::gs -> (g, gs)
             | [] -> failwith "Pointwise: no goals"  in
           match uu____5376 with
           | (g,gs) ->
               let gt1 = g.FStar_Tactics_Types.goal_ty  in
               (log ps
                  (fun uu____5413  ->
                     let uu____5414 = FStar_Syntax_Print.term_to_string gt1
                        in
                     FStar_Util.print1 "Pointwise starting with %s\n"
                       uu____5414);
                bind dismiss_all
                  (fun uu____5417  ->
                     let uu____5418 =
                       tac_fold_env d
                         (pointwise_rec ps tau g.FStar_Tactics_Types.opts)
                         g.FStar_Tactics_Types.context gt1
                        in
                     bind uu____5418
                       (fun gt'  ->
                          log ps
                            (fun uu____5428  ->
                               let uu____5429 =
                                 FStar_Syntax_Print.term_to_string gt'  in
                               FStar_Util.print1
                                 "Pointwise seems to have succeded with %s\n"
                                 uu____5429);
                          (let uu____5430 = push_goals gs  in
                           bind uu____5430
                             (fun uu____5434  ->
                                add_goals
                                  [(let uu___104_5436 = g  in
                                    {
                                      FStar_Tactics_Types.context =
                                        (uu___104_5436.FStar_Tactics_Types.context);
                                      FStar_Tactics_Types.witness =
                                        (uu___104_5436.FStar_Tactics_Types.witness);
                                      FStar_Tactics_Types.goal_ty = gt';
                                      FStar_Tactics_Types.opts =
                                        (uu___104_5436.FStar_Tactics_Types.opts);
                                      FStar_Tactics_Types.is_guard =
                                        (uu___104_5436.FStar_Tactics_Types.is_guard)
                                    })]))))))
  
let (trefl : Prims.unit tac) =
  bind cur_goal
    (fun g  ->
       let uu____5458 =
         FStar_Syntax_Util.un_squash g.FStar_Tactics_Types.goal_ty  in
       match uu____5458 with
       | FStar_Pervasives_Native.Some t ->
           let uu____5470 = FStar_Syntax_Util.head_and_args' t  in
           (match uu____5470 with
            | (hd1,args) ->
                let uu____5503 =
                  let uu____5516 =
                    let uu____5517 = FStar_Syntax_Util.un_uinst hd1  in
                    uu____5517.FStar_Syntax_Syntax.n  in
                  (uu____5516, args)  in
                (match uu____5503 with
                 | (FStar_Syntax_Syntax.Tm_fvar
                    fv,uu____5531::(l,uu____5533)::(r,uu____5535)::[]) when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.eq2_lid
                     ->
                     let uu____5582 =
                       let uu____5583 =
                         do_unify g.FStar_Tactics_Types.context l r  in
                       Prims.op_Negation uu____5583  in
                     if uu____5582
                     then
                       let uu____5586 = tts g.FStar_Tactics_Types.context l
                          in
                       let uu____5587 = tts g.FStar_Tactics_Types.context r
                          in
                       fail2 "trefl: not a trivial equality (%s vs %s)"
                         uu____5586 uu____5587
                     else solve g FStar_Syntax_Util.exp_unit
                 | (hd2,uu____5590) ->
                     let uu____5607 = tts g.FStar_Tactics_Types.context t  in
                     fail1 "trefl: not an equality (%s)" uu____5607))
       | FStar_Pervasives_Native.None  -> fail "not an irrelevant goal")
  
let (dup : Prims.unit tac) =
  bind cur_goal
    (fun g  ->
       let uu____5617 =
         new_uvar "dup" g.FStar_Tactics_Types.context
           g.FStar_Tactics_Types.goal_ty
          in
       bind uu____5617
         (fun u  ->
            let g' =
              let uu___105_5624 = g  in
              {
                FStar_Tactics_Types.context =
                  (uu___105_5624.FStar_Tactics_Types.context);
                FStar_Tactics_Types.witness = u;
                FStar_Tactics_Types.goal_ty =
                  (uu___105_5624.FStar_Tactics_Types.goal_ty);
                FStar_Tactics_Types.opts =
                  (uu___105_5624.FStar_Tactics_Types.opts);
                FStar_Tactics_Types.is_guard =
                  (uu___105_5624.FStar_Tactics_Types.is_guard)
              }  in
            bind dismiss
              (fun uu____5627  ->
                 let uu____5628 =
                   let uu____5631 =
                     let uu____5632 =
                       FStar_TypeChecker_TcTerm.universe_of
                         g.FStar_Tactics_Types.context
                         g.FStar_Tactics_Types.goal_ty
                        in
                     FStar_Syntax_Util.mk_eq2 uu____5632
                       g.FStar_Tactics_Types.goal_ty u
                       g.FStar_Tactics_Types.witness
                      in
                   add_irrelevant_goal "dup equation"
                     g.FStar_Tactics_Types.context uu____5631
                     g.FStar_Tactics_Types.opts
                    in
                 bind uu____5628
                   (fun uu____5635  ->
                      let uu____5636 = add_goals [g']  in
                      bind uu____5636 (fun uu____5640  -> ret ())))))
  
let (flip : Prims.unit tac) =
  bind get
    (fun ps  ->
       match ps.FStar_Tactics_Types.goals with
       | g1::g2::gs ->
           set
             (let uu___106_5659 = ps  in
              {
                FStar_Tactics_Types.main_context =
                  (uu___106_5659.FStar_Tactics_Types.main_context);
                FStar_Tactics_Types.main_goal =
                  (uu___106_5659.FStar_Tactics_Types.main_goal);
                FStar_Tactics_Types.all_implicits =
                  (uu___106_5659.FStar_Tactics_Types.all_implicits);
                FStar_Tactics_Types.goals = (g2 :: g1 :: gs);
                FStar_Tactics_Types.smt_goals =
                  (uu___106_5659.FStar_Tactics_Types.smt_goals);
                FStar_Tactics_Types.depth =
                  (uu___106_5659.FStar_Tactics_Types.depth);
                FStar_Tactics_Types.__dump =
                  (uu___106_5659.FStar_Tactics_Types.__dump);
                FStar_Tactics_Types.psc =
                  (uu___106_5659.FStar_Tactics_Types.psc);
                FStar_Tactics_Types.entry_range =
                  (uu___106_5659.FStar_Tactics_Types.entry_range)
              })
       | uu____5660 -> fail "flip: less than 2 goals")
  
let (later : Prims.unit tac) =
  bind get
    (fun ps  ->
       match ps.FStar_Tactics_Types.goals with
       | [] -> ret ()
       | g::gs ->
           set
             (let uu___107_5677 = ps  in
              {
                FStar_Tactics_Types.main_context =
                  (uu___107_5677.FStar_Tactics_Types.main_context);
                FStar_Tactics_Types.main_goal =
                  (uu___107_5677.FStar_Tactics_Types.main_goal);
                FStar_Tactics_Types.all_implicits =
                  (uu___107_5677.FStar_Tactics_Types.all_implicits);
                FStar_Tactics_Types.goals = (FStar_List.append gs [g]);
                FStar_Tactics_Types.smt_goals =
                  (uu___107_5677.FStar_Tactics_Types.smt_goals);
                FStar_Tactics_Types.depth =
                  (uu___107_5677.FStar_Tactics_Types.depth);
                FStar_Tactics_Types.__dump =
                  (uu___107_5677.FStar_Tactics_Types.__dump);
                FStar_Tactics_Types.psc =
                  (uu___107_5677.FStar_Tactics_Types.psc);
                FStar_Tactics_Types.entry_range =
                  (uu___107_5677.FStar_Tactics_Types.entry_range)
              }))
  
let (qed : Prims.unit tac) =
  bind get
    (fun ps  ->
       match ps.FStar_Tactics_Types.goals with
       | [] -> ret ()
       | uu____5686 -> fail "Not done!")
  
let (cases :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 tac)
  =
  fun t  ->
    let uu____5704 =
      bind cur_goal
        (fun g  ->
           let uu____5718 = __tc g.FStar_Tactics_Types.context t  in
           bind uu____5718
             (fun uu____5754  ->
                match uu____5754 with
                | (t1,typ,guard) ->
                    let uu____5770 = FStar_Syntax_Util.head_and_args typ  in
                    (match uu____5770 with
                     | (hd1,args) ->
                         let uu____5813 =
                           let uu____5826 =
                             let uu____5827 = FStar_Syntax_Util.un_uinst hd1
                                in
                             uu____5827.FStar_Syntax_Syntax.n  in
                           (uu____5826, args)  in
                         (match uu____5813 with
                          | (FStar_Syntax_Syntax.Tm_fvar
                             fv,(p,uu____5846)::(q,uu____5848)::[]) when
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
                                let uu___108_5886 = g  in
                                let uu____5887 =
                                  FStar_TypeChecker_Env.push_bv
                                    g.FStar_Tactics_Types.context v_p
                                   in
                                {
                                  FStar_Tactics_Types.context = uu____5887;
                                  FStar_Tactics_Types.witness =
                                    (uu___108_5886.FStar_Tactics_Types.witness);
                                  FStar_Tactics_Types.goal_ty =
                                    (uu___108_5886.FStar_Tactics_Types.goal_ty);
                                  FStar_Tactics_Types.opts =
                                    (uu___108_5886.FStar_Tactics_Types.opts);
                                  FStar_Tactics_Types.is_guard =
                                    (uu___108_5886.FStar_Tactics_Types.is_guard)
                                }  in
                              let g2 =
                                let uu___109_5889 = g  in
                                let uu____5890 =
                                  FStar_TypeChecker_Env.push_bv
                                    g.FStar_Tactics_Types.context v_q
                                   in
                                {
                                  FStar_Tactics_Types.context = uu____5890;
                                  FStar_Tactics_Types.witness =
                                    (uu___109_5889.FStar_Tactics_Types.witness);
                                  FStar_Tactics_Types.goal_ty =
                                    (uu___109_5889.FStar_Tactics_Types.goal_ty);
                                  FStar_Tactics_Types.opts =
                                    (uu___109_5889.FStar_Tactics_Types.opts);
                                  FStar_Tactics_Types.is_guard =
                                    (uu___109_5889.FStar_Tactics_Types.is_guard)
                                }  in
                              bind dismiss
                                (fun uu____5897  ->
                                   let uu____5898 = add_goals [g1; g2]  in
                                   bind uu____5898
                                     (fun uu____5907  ->
                                        let uu____5908 =
                                          let uu____5913 =
                                            FStar_Syntax_Syntax.bv_to_name
                                              v_p
                                             in
                                          let uu____5914 =
                                            FStar_Syntax_Syntax.bv_to_name
                                              v_q
                                             in
                                          (uu____5913, uu____5914)  in
                                        ret uu____5908))
                          | uu____5919 ->
                              let uu____5932 =
                                tts g.FStar_Tactics_Types.context typ  in
                              fail1 "Not a disjunction: %s" uu____5932))))
       in
    FStar_All.pipe_left (wrap_err "cases") uu____5704
  
let (set_options : Prims.string -> Prims.unit tac) =
  fun s  ->
    bind cur_goal
      (fun g  ->
         FStar_Options.push ();
         (let uu____5970 = FStar_Util.smap_copy g.FStar_Tactics_Types.opts
             in
          FStar_Options.set uu____5970);
         (let res = FStar_Options.set_options FStar_Options.Set s  in
          let opts' = FStar_Options.peek ()  in
          FStar_Options.pop ();
          (match res with
           | FStar_Getopt.Success  ->
               let g' =
                 let uu___110_5977 = g  in
                 {
                   FStar_Tactics_Types.context =
                     (uu___110_5977.FStar_Tactics_Types.context);
                   FStar_Tactics_Types.witness =
                     (uu___110_5977.FStar_Tactics_Types.witness);
                   FStar_Tactics_Types.goal_ty =
                     (uu___110_5977.FStar_Tactics_Types.goal_ty);
                   FStar_Tactics_Types.opts = opts';
                   FStar_Tactics_Types.is_guard =
                     (uu___110_5977.FStar_Tactics_Types.is_guard)
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
      let uu____6021 =
        bind cur_goal
          (fun goal  ->
             let env =
               FStar_TypeChecker_Env.set_expected_typ
                 goal.FStar_Tactics_Types.context ty
                in
             let uu____6029 = __tc env tm  in
             bind uu____6029
               (fun uu____6049  ->
                  match uu____6049 with
                  | (tm1,typ,guard) ->
                      (FStar_TypeChecker_Rel.force_trivial_guard env guard;
                       ret tm1)))
         in
      FStar_All.pipe_left (wrap_err "unquote") uu____6021
  
let (uvar_env :
  env ->
    FStar_Syntax_Syntax.typ FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.term tac)
  =
  fun env  ->
    fun ty  ->
      let uu____6080 =
        match ty with
        | FStar_Pervasives_Native.Some ty1 -> ret ty1
        | FStar_Pervasives_Native.None  ->
            let uu____6086 =
              let uu____6087 = FStar_Syntax_Util.type_u ()  in
              FStar_All.pipe_left FStar_Pervasives_Native.fst uu____6087  in
            new_uvar "uvar_env.2" env uu____6086
         in
      bind uu____6080
        (fun typ  ->
           let uu____6099 = new_uvar "uvar_env" env typ  in
           bind uu____6099 (fun t  -> ret t))
  
let (unshelve : FStar_Syntax_Syntax.term -> Prims.unit tac) =
  fun t  ->
    let uu____6111 =
      bind cur_goal
        (fun goal  ->
           let uu____6117 = __tc goal.FStar_Tactics_Types.context t  in
           bind uu____6117
             (fun uu____6137  ->
                match uu____6137 with
                | (t1,typ,guard) ->
                    let uu____6149 =
                      must_trivial goal.FStar_Tactics_Types.context guard  in
                    bind uu____6149
                      (fun uu____6154  ->
                         let uu____6155 =
                           let uu____6158 =
                             let uu___111_6159 = goal  in
                             let uu____6160 =
                               bnorm goal.FStar_Tactics_Types.context t1  in
                             let uu____6161 =
                               bnorm goal.FStar_Tactics_Types.context typ  in
                             {
                               FStar_Tactics_Types.context =
                                 (uu___111_6159.FStar_Tactics_Types.context);
                               FStar_Tactics_Types.witness = uu____6160;
                               FStar_Tactics_Types.goal_ty = uu____6161;
                               FStar_Tactics_Types.opts =
                                 (uu___111_6159.FStar_Tactics_Types.opts);
                               FStar_Tactics_Types.is_guard = false
                             }  in
                           [uu____6158]  in
                         add_goals uu____6155)))
       in
    FStar_All.pipe_left (wrap_err "unshelve") uu____6111
  
let (unify :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool tac) =
  fun t1  ->
    fun t2  ->
      bind get
        (fun ps  ->
           let uu____6179 =
             do_unify ps.FStar_Tactics_Types.main_context t1 t2  in
           ret uu____6179)
  
let (launch_process :
  Prims.string -> Prims.string -> Prims.string -> Prims.string tac) =
  fun prog  ->
    fun args  ->
      fun input  ->
        bind idtac
          (fun uu____6196  ->
             let uu____6197 = FStar_Options.unsafe_tactic_exec ()  in
             if uu____6197
             then
               let s =
                 FStar_Util.launch_process true "tactic_launch" prog args
                   input (fun uu____6203  -> fun uu____6204  -> false)
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
      let uu____6220 =
        FStar_TypeChecker_Util.new_implicit_var "proofstate_of_goal_ty"
          typ.FStar_Syntax_Syntax.pos env typ
         in
      match uu____6220 with
      | (u,uu____6238,g_u) ->
          let g =
            let uu____6253 = FStar_Options.peek ()  in
            {
              FStar_Tactics_Types.context = env;
              FStar_Tactics_Types.witness = u;
              FStar_Tactics_Types.goal_ty = typ;
              FStar_Tactics_Types.opts = uu____6253;
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
      let uu____6264 = goal_of_goal_ty env typ  in
      match uu____6264 with
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
  