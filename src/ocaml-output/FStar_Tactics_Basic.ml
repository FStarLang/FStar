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
                let uu____434 =
                  let uu____439 =
                    let uu____440 =
                      FStar_List.map goal_to_json
                        ps.FStar_Tactics_Types.goals
                       in
                    FStar_Util.JsonList uu____440  in
                  ("goals", uu____439)  in
                let uu____443 =
                  let uu____450 =
                    let uu____455 =
                      let uu____456 =
                        FStar_List.map goal_to_json
                          ps.FStar_Tactics_Types.smt_goals
                         in
                      FStar_Util.JsonList uu____456  in
                    ("smt-goals", uu____455)  in
                  [uu____450]  in
                uu____434 :: uu____443  in
              ("depth", (FStar_Util.JsonInt (ps.FStar_Tactics_Types.depth)))
                :: uu____427
               in
            uu____414 :: uu____420  in
          ("label", (FStar_Util.JsonStr msg)) :: uu____407  in
        FStar_Util.JsonAssoc uu____400
  
let (dump_proofstate :
  FStar_Tactics_Types.proofstate -> Prims.string -> Prims.unit) =
  fun ps  ->
    fun msg  ->
      FStar_Options.with_saved_options
        (fun uu____491  ->
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
         (let uu____512 = FStar_Tactics_Types.subst_proof_state subst1 ps  in
          dump_cur uu____512 msg);
         FStar_Tactics_Result.Success ((), ps))
  
let (print_proof_state : Prims.string -> Prims.unit tac) =
  fun msg  ->
    mk_tac
      (fun ps  ->
         let psc = ps.FStar_Tactics_Types.psc  in
         let subst1 = FStar_TypeChecker_Normalize.psc_subst psc  in
         (let uu____528 = FStar_Tactics_Types.subst_proof_state subst1 ps  in
          dump_proofstate uu____528 msg);
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
      let uu____563 = FStar_ST.op_Bang tac_verb_dbg  in
      match uu____563 with
      | FStar_Pervasives_Native.None  ->
          ((let uu____590 =
              let uu____593 =
                FStar_TypeChecker_Env.debug
                  ps.FStar_Tactics_Types.main_context
                  (FStar_Options.Other "TacVerbose")
                 in
              FStar_Pervasives_Native.Some uu____593  in
            FStar_ST.op_Colon_Equals tac_verb_dbg uu____590);
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
         (let uu____662 =
            FStar_TypeChecker_Env.debug ps.FStar_Tactics_Types.main_context
              (FStar_Options.Other "TacFail")
             in
          if uu____662
          then dump_proofstate ps (Prims.strcat "TACTING FAILING: " msg)
          else ());
         FStar_Tactics_Result.Failed (msg, ps))
  
let fail1 : 'Auu____667 . Prims.string -> Prims.string -> 'Auu____667 tac =
  fun msg  ->
    fun x  -> let uu____678 = FStar_Util.format1 msg x  in fail uu____678
  
let fail2 :
  'Auu____683 .
    Prims.string -> Prims.string -> Prims.string -> 'Auu____683 tac
  =
  fun msg  ->
    fun x  ->
      fun y  -> let uu____698 = FStar_Util.format2 msg x y  in fail uu____698
  
let fail3 :
  'Auu____704 .
    Prims.string ->
      Prims.string -> Prims.string -> Prims.string -> 'Auu____704 tac
  =
  fun msg  ->
    fun x  ->
      fun y  ->
        fun z  ->
          let uu____723 = FStar_Util.format3 msg x y z  in fail uu____723
  
let fail4 :
  'Auu____730 .
    Prims.string ->
      Prims.string ->
        Prims.string -> Prims.string -> Prims.string -> 'Auu____730 tac
  =
  fun msg  ->
    fun x  ->
      fun y  ->
        fun z  ->
          fun w  ->
            let uu____753 = FStar_Util.format4 msg x y z w  in fail uu____753
  
let trytac' : 'a . 'a tac -> (Prims.string,'a) FStar_Util.either tac =
  fun t  ->
    mk_tac
      (fun ps  ->
         let tx = FStar_Syntax_Unionfind.new_transaction ()  in
         let uu____783 = run t ps  in
         match uu____783 with
         | FStar_Tactics_Result.Success (a,q) ->
             (FStar_Syntax_Unionfind.commit tx;
              FStar_Tactics_Result.Success ((FStar_Util.Inr a), q))
         | FStar_Tactics_Result.Failed (m,uu____804) ->
             (FStar_Syntax_Unionfind.rollback tx;
              FStar_Tactics_Result.Success ((FStar_Util.Inl m), ps)))
  
let trytac : 'a . 'a tac -> 'a FStar_Pervasives_Native.option tac =
  fun t  ->
    let uu____829 = trytac' t  in
    bind uu____829
      (fun r  ->
         match r with
         | FStar_Util.Inr v1 -> ret (FStar_Pervasives_Native.Some v1)
         | FStar_Util.Inl uu____856 -> ret FStar_Pervasives_Native.None)
  
let wrap_err : 'a . Prims.string -> 'a tac -> 'a tac =
  fun pref  ->
    fun t  ->
      mk_tac
        (fun ps  ->
           let uu____882 = run t ps  in
           match uu____882 with
           | FStar_Tactics_Result.Success (a,q) ->
               FStar_Tactics_Result.Success (a, q)
           | FStar_Tactics_Result.Failed (msg,q) ->
               FStar_Tactics_Result.Failed
                 ((Prims.strcat pref (Prims.strcat ": " msg)), q))
  
let (set : FStar_Tactics_Types.proofstate -> Prims.unit tac) =
  fun p  -> mk_tac (fun uu____899  -> FStar_Tactics_Result.Success ((), p)) 
let (do_unify :
  env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let debug_on uu____912 =
          let uu____913 =
            FStar_Options.set_options FStar_Options.Set
              "--debug_level Rel --debug_level RelCheck"
             in
          ()  in
        let debug_off uu____917 =
          let uu____918 = FStar_Options.set_options FStar_Options.Reset ""
             in
          ()  in
        (let uu____920 =
           FStar_TypeChecker_Env.debug env (FStar_Options.Other "1346")  in
         if uu____920
         then
           (debug_on ();
            (let uu____922 = FStar_Syntax_Print.term_to_string t1  in
             let uu____923 = FStar_Syntax_Print.term_to_string t2  in
             FStar_Util.print2 "%%%%%%%%do_unify %s =? %s\n" uu____922
               uu____923))
         else ());
        (try
           let res = FStar_TypeChecker_Rel.teq_nosmt env t1 t2  in
           debug_off (); res
         with | uu____935 -> (debug_off (); false))
  
let (trysolve :
  FStar_Tactics_Types.goal -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun goal  ->
    fun solution  ->
      do_unify goal.FStar_Tactics_Types.context solution
        goal.FStar_Tactics_Types.witness
  
let (dismiss : Prims.unit tac) =
  bind get
    (fun p  ->
       let uu____948 =
         let uu___61_949 = p  in
         let uu____950 = FStar_List.tl p.FStar_Tactics_Types.goals  in
         {
           FStar_Tactics_Types.main_context =
             (uu___61_949.FStar_Tactics_Types.main_context);
           FStar_Tactics_Types.main_goal =
             (uu___61_949.FStar_Tactics_Types.main_goal);
           FStar_Tactics_Types.all_implicits =
             (uu___61_949.FStar_Tactics_Types.all_implicits);
           FStar_Tactics_Types.goals = uu____950;
           FStar_Tactics_Types.smt_goals =
             (uu___61_949.FStar_Tactics_Types.smt_goals);
           FStar_Tactics_Types.depth =
             (uu___61_949.FStar_Tactics_Types.depth);
           FStar_Tactics_Types.__dump =
             (uu___61_949.FStar_Tactics_Types.__dump);
           FStar_Tactics_Types.psc = (uu___61_949.FStar_Tactics_Types.psc);
           FStar_Tactics_Types.entry_range =
             (uu___61_949.FStar_Tactics_Types.entry_range)
         }  in
       set uu____948)
  
let (solve :
  FStar_Tactics_Types.goal -> FStar_Syntax_Syntax.term -> Prims.unit tac) =
  fun goal  ->
    fun solution  ->
      let uu____963 = trysolve goal solution  in
      if uu____963
      then dismiss
      else
        (let uu____967 =
           let uu____968 = tts goal.FStar_Tactics_Types.context solution  in
           let uu____969 =
             tts goal.FStar_Tactics_Types.context
               goal.FStar_Tactics_Types.witness
              in
           let uu____970 =
             tts goal.FStar_Tactics_Types.context
               goal.FStar_Tactics_Types.goal_ty
              in
           FStar_Util.format3 "%s does not solve %s : %s" uu____968 uu____969
             uu____970
            in
         fail uu____967)
  
let (dismiss_all : Prims.unit tac) =
  bind get
    (fun p  ->
       set
         (let uu___62_977 = p  in
          {
            FStar_Tactics_Types.main_context =
              (uu___62_977.FStar_Tactics_Types.main_context);
            FStar_Tactics_Types.main_goal =
              (uu___62_977.FStar_Tactics_Types.main_goal);
            FStar_Tactics_Types.all_implicits =
              (uu___62_977.FStar_Tactics_Types.all_implicits);
            FStar_Tactics_Types.goals = [];
            FStar_Tactics_Types.smt_goals =
              (uu___62_977.FStar_Tactics_Types.smt_goals);
            FStar_Tactics_Types.depth =
              (uu___62_977.FStar_Tactics_Types.depth);
            FStar_Tactics_Types.__dump =
              (uu___62_977.FStar_Tactics_Types.__dump);
            FStar_Tactics_Types.psc = (uu___62_977.FStar_Tactics_Types.psc);
            FStar_Tactics_Types.entry_range =
              (uu___62_977.FStar_Tactics_Types.entry_range)
          }))
  
let (nwarn : Prims.int FStar_ST.ref) =
  FStar_Util.mk_ref (Prims.parse_int "0") 
let (check_valid_goal : FStar_Tactics_Types.goal -> Prims.unit) =
  fun g  ->
    let uu____994 = FStar_Options.defensive ()  in
    if uu____994
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
        let uu____1006 = FStar_TypeChecker_Env.pop_bv e  in
        match uu____1006 with
        | FStar_Pervasives_Native.None  -> b3
        | FStar_Pervasives_Native.Some (bv,e1) ->
            let b4 =
              b3 &&
                (FStar_TypeChecker_Env.closed e1 bv.FStar_Syntax_Syntax.sort)
               in
            aux b4 e1
         in
      let uu____1024 =
        (let uu____1027 = aux b2 env  in Prims.op_Negation uu____1027) &&
          (let uu____1029 = FStar_ST.op_Bang nwarn  in
           uu____1029 < (Prims.parse_int "5"))
         in
      (if uu____1024
       then
         ((let uu____1050 =
             let uu____1055 =
               let uu____1056 = goal_to_string g  in
               FStar_Util.format1
                 "The following goal is ill-formed. Keeping calm and carrying on...\n<%s>\n\n"
                 uu____1056
                in
             (FStar_Errors.Warning_IllFormedGoal, uu____1055)  in
           FStar_Errors.log_issue
             (g.FStar_Tactics_Types.goal_ty).FStar_Syntax_Syntax.pos
             uu____1050);
          (let uu____1057 =
             let uu____1058 = FStar_ST.op_Bang nwarn  in
             uu____1058 + (Prims.parse_int "1")  in
           FStar_ST.op_Colon_Equals nwarn uu____1057))
       else ())
    else ()
  
let (add_goals : FStar_Tactics_Types.goal Prims.list -> Prims.unit tac) =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___63_1116 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___63_1116.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___63_1116.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___63_1116.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (FStar_List.append gs p.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___63_1116.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___63_1116.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___63_1116.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___63_1116.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___63_1116.FStar_Tactics_Types.entry_range)
            }))
  
let (add_smt_goals : FStar_Tactics_Types.goal Prims.list -> Prims.unit tac) =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___64_1134 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___64_1134.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___64_1134.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___64_1134.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___64_1134.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (FStar_List.append gs p.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___64_1134.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___64_1134.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___64_1134.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___64_1134.FStar_Tactics_Types.entry_range)
            }))
  
let (push_goals : FStar_Tactics_Types.goal Prims.list -> Prims.unit tac) =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___65_1152 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___65_1152.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___65_1152.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___65_1152.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (FStar_List.append p.FStar_Tactics_Types.goals gs);
              FStar_Tactics_Types.smt_goals =
                (uu___65_1152.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___65_1152.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___65_1152.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___65_1152.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___65_1152.FStar_Tactics_Types.entry_range)
            }))
  
let (push_smt_goals : FStar_Tactics_Types.goal Prims.list -> Prims.unit tac)
  =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___66_1170 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___66_1170.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___66_1170.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___66_1170.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___66_1170.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (FStar_List.append p.FStar_Tactics_Types.smt_goals gs);
              FStar_Tactics_Types.depth =
                (uu___66_1170.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___66_1170.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___66_1170.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___66_1170.FStar_Tactics_Types.entry_range)
            }))
  
let (replace_cur : FStar_Tactics_Types.goal -> Prims.unit tac) =
  fun g  -> bind dismiss (fun uu____1179  -> add_goals [g]) 
let (add_implicits : implicits -> Prims.unit tac) =
  fun i  ->
    bind get
      (fun p  ->
         set
           (let uu___67_1191 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___67_1191.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___67_1191.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (FStar_List.append i p.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___67_1191.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___67_1191.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___67_1191.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___67_1191.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___67_1191.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___67_1191.FStar_Tactics_Types.entry_range)
            }))
  
let (new_uvar :
  Prims.string ->
    env -> FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.term tac)
  =
  fun reason  ->
    fun env  ->
      fun typ  ->
        let uu____1217 =
          FStar_TypeChecker_Util.new_implicit_var reason
            typ.FStar_Syntax_Syntax.pos env typ
           in
        match uu____1217 with
        | (u,uu____1233,g_u) ->
            let uu____1247 =
              add_implicits g_u.FStar_TypeChecker_Env.implicits  in
            bind uu____1247 (fun uu____1251  -> ret u)
  
let (is_true : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____1255 = FStar_Syntax_Util.un_squash t  in
    match uu____1255 with
    | FStar_Pervasives_Native.Some t' ->
        let uu____1265 =
          let uu____1266 = FStar_Syntax_Subst.compress t'  in
          uu____1266.FStar_Syntax_Syntax.n  in
        (match uu____1265 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.true_lid
         | uu____1270 -> false)
    | uu____1271 -> false
  
let (is_false : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____1279 = FStar_Syntax_Util.un_squash t  in
    match uu____1279 with
    | FStar_Pervasives_Native.Some t' ->
        let uu____1289 =
          let uu____1290 = FStar_Syntax_Subst.compress t'  in
          uu____1290.FStar_Syntax_Syntax.n  in
        (match uu____1289 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.false_lid
         | uu____1294 -> false)
    | uu____1295 -> false
  
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
            let uu____1335 = env.FStar_TypeChecker_Env.universe_of env phi
               in
            FStar_Syntax_Util.mk_squash uu____1335 phi  in
          let uu____1336 = new_uvar reason env typ  in
          bind uu____1336
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
             let uu____1392 =
               (ps.FStar_Tactics_Types.main_context).FStar_TypeChecker_Env.type_of
                 e t
                in
             ret uu____1392
           with
           | ex ->
               let uu____1419 = tts e t  in
               let uu____1420 =
                 let uu____1421 = FStar_TypeChecker_Env.all_binders e  in
                 FStar_All.pipe_right uu____1421
                   (FStar_Syntax_Print.binders_to_string ", ")
                  in
               fail2 "Cannot type %s in context (%s)" uu____1419 uu____1420)
  
let (must_trivial : env -> FStar_TypeChecker_Env.guard_t -> Prims.unit tac) =
  fun e  ->
    fun g  ->
      try
        let uu____1445 =
          let uu____1446 =
            let uu____1447 = FStar_TypeChecker_Rel.discharge_guard_no_smt e g
               in
            FStar_All.pipe_left FStar_TypeChecker_Rel.is_trivial uu____1447
             in
          Prims.op_Negation uu____1446  in
        if uu____1445 then fail "got non-trivial guard" else ret ()
      with | uu____1456 -> fail "got non-trivial guard"
  
let (tc : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.typ tac) =
  fun t  ->
    let uu____1464 =
      bind cur_goal
        (fun goal  ->
           let uu____1470 = __tc goal.FStar_Tactics_Types.context t  in
           bind uu____1470
             (fun uu____1490  ->
                match uu____1490 with
                | (t1,typ,guard) ->
                    let uu____1502 =
                      must_trivial goal.FStar_Tactics_Types.context guard  in
                    bind uu____1502 (fun uu____1506  -> ret typ)))
       in
    FStar_All.pipe_left (wrap_err "tc") uu____1464
  
let (add_irrelevant_goal :
  Prims.string ->
    env ->
      FStar_Syntax_Syntax.typ -> FStar_Options.optionstate -> Prims.unit tac)
  =
  fun reason  ->
    fun env  ->
      fun phi  ->
        fun opts  ->
          let uu____1527 = mk_irrelevant_goal reason env phi opts  in
          bind uu____1527 (fun goal  -> add_goals [goal])
  
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
       let uu____1549 =
         istrivial goal.FStar_Tactics_Types.context
           goal.FStar_Tactics_Types.goal_ty
          in
       if uu____1549
       then solve goal FStar_Syntax_Util.exp_unit
       else
         (let uu____1553 =
            tts goal.FStar_Tactics_Types.context
              goal.FStar_Tactics_Types.goal_ty
             in
          fail1 "Not a trivial goal: %s" uu____1553))
  
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
          let uu____1570 =
            let uu____1571 = FStar_TypeChecker_Rel.simplify_guard e g  in
            uu____1571.FStar_TypeChecker_Env.guard_f  in
          match uu____1570 with
          | FStar_TypeChecker_Common.Trivial  -> ret ()
          | FStar_TypeChecker_Common.NonTrivial f ->
              let uu____1575 = istrivial e f  in
              if uu____1575
              then ret ()
              else
                (let uu____1579 = mk_irrelevant_goal reason e f opts  in
                 bind uu____1579
                   (fun goal  ->
                      let goal1 =
                        let uu___72_1586 = goal  in
                        {
                          FStar_Tactics_Types.context =
                            (uu___72_1586.FStar_Tactics_Types.context);
                          FStar_Tactics_Types.witness =
                            (uu___72_1586.FStar_Tactics_Types.witness);
                          FStar_Tactics_Types.goal_ty =
                            (uu___72_1586.FStar_Tactics_Types.goal_ty);
                          FStar_Tactics_Types.opts =
                            (uu___72_1586.FStar_Tactics_Types.opts);
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
          let uu____1607 =
            let uu____1608 = FStar_TypeChecker_Rel.simplify_guard e g  in
            uu____1608.FStar_TypeChecker_Env.guard_f  in
          match uu____1607 with
          | FStar_TypeChecker_Common.Trivial  ->
              ret FStar_Pervasives_Native.None
          | FStar_TypeChecker_Common.NonTrivial f ->
              let uu____1616 = istrivial e f  in
              if uu____1616
              then ret FStar_Pervasives_Native.None
              else
                (let uu____1624 = mk_irrelevant_goal reason e f opts  in
                 bind uu____1624
                   (fun goal  ->
                      ret
                        (FStar_Pervasives_Native.Some
                           (let uu___73_1634 = goal  in
                            {
                              FStar_Tactics_Types.context =
                                (uu___73_1634.FStar_Tactics_Types.context);
                              FStar_Tactics_Types.witness =
                                (uu___73_1634.FStar_Tactics_Types.witness);
                              FStar_Tactics_Types.goal_ty =
                                (uu___73_1634.FStar_Tactics_Types.goal_ty);
                              FStar_Tactics_Types.opts =
                                (uu___73_1634.FStar_Tactics_Types.opts);
                              FStar_Tactics_Types.is_guard = true
                            }))))
  
let (smt : Prims.unit tac) =
  bind cur_goal
    (fun g  ->
       let uu____1642 = is_irrelevant g  in
       if uu____1642
       then bind dismiss (fun uu____1646  -> add_smt_goals [g])
       else
         (let uu____1648 =
            tts g.FStar_Tactics_Types.context g.FStar_Tactics_Types.goal_ty
             in
          fail1 "goal is not irrelevant: cannot dispatch to smt (%s)"
            uu____1648))
  
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
             let uu____1689 =
               try
                 let uu____1723 =
                   let uu____1732 = FStar_BigInt.to_int_fs n1  in
                   FStar_List.splitAt uu____1732 p.FStar_Tactics_Types.goals
                    in
                 ret uu____1723
               with | uu____1754 -> fail "divide: not enough goals"  in
             bind uu____1689
               (fun uu____1781  ->
                  match uu____1781 with
                  | (lgs,rgs) ->
                      let lp =
                        let uu___74_1807 = p  in
                        {
                          FStar_Tactics_Types.main_context =
                            (uu___74_1807.FStar_Tactics_Types.main_context);
                          FStar_Tactics_Types.main_goal =
                            (uu___74_1807.FStar_Tactics_Types.main_goal);
                          FStar_Tactics_Types.all_implicits =
                            (uu___74_1807.FStar_Tactics_Types.all_implicits);
                          FStar_Tactics_Types.goals = lgs;
                          FStar_Tactics_Types.smt_goals = [];
                          FStar_Tactics_Types.depth =
                            (uu___74_1807.FStar_Tactics_Types.depth);
                          FStar_Tactics_Types.__dump =
                            (uu___74_1807.FStar_Tactics_Types.__dump);
                          FStar_Tactics_Types.psc =
                            (uu___74_1807.FStar_Tactics_Types.psc);
                          FStar_Tactics_Types.entry_range =
                            (uu___74_1807.FStar_Tactics_Types.entry_range)
                        }  in
                      let rp =
                        let uu___75_1809 = p  in
                        {
                          FStar_Tactics_Types.main_context =
                            (uu___75_1809.FStar_Tactics_Types.main_context);
                          FStar_Tactics_Types.main_goal =
                            (uu___75_1809.FStar_Tactics_Types.main_goal);
                          FStar_Tactics_Types.all_implicits =
                            (uu___75_1809.FStar_Tactics_Types.all_implicits);
                          FStar_Tactics_Types.goals = rgs;
                          FStar_Tactics_Types.smt_goals = [];
                          FStar_Tactics_Types.depth =
                            (uu___75_1809.FStar_Tactics_Types.depth);
                          FStar_Tactics_Types.__dump =
                            (uu___75_1809.FStar_Tactics_Types.__dump);
                          FStar_Tactics_Types.psc =
                            (uu___75_1809.FStar_Tactics_Types.psc);
                          FStar_Tactics_Types.entry_range =
                            (uu___75_1809.FStar_Tactics_Types.entry_range)
                        }  in
                      let uu____1810 = set lp  in
                      bind uu____1810
                        (fun uu____1818  ->
                           bind l
                             (fun a  ->
                                bind get
                                  (fun lp'  ->
                                     let uu____1832 = set rp  in
                                     bind uu____1832
                                       (fun uu____1840  ->
                                          bind r
                                            (fun b  ->
                                               bind get
                                                 (fun rp'  ->
                                                    let p' =
                                                      let uu___76_1856 = p
                                                         in
                                                      {
                                                        FStar_Tactics_Types.main_context
                                                          =
                                                          (uu___76_1856.FStar_Tactics_Types.main_context);
                                                        FStar_Tactics_Types.main_goal
                                                          =
                                                          (uu___76_1856.FStar_Tactics_Types.main_goal);
                                                        FStar_Tactics_Types.all_implicits
                                                          =
                                                          (uu___76_1856.FStar_Tactics_Types.all_implicits);
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
                                                          (uu___76_1856.FStar_Tactics_Types.depth);
                                                        FStar_Tactics_Types.__dump
                                                          =
                                                          (uu___76_1856.FStar_Tactics_Types.__dump);
                                                        FStar_Tactics_Types.psc
                                                          =
                                                          (uu___76_1856.FStar_Tactics_Types.psc);
                                                        FStar_Tactics_Types.entry_range
                                                          =
                                                          (uu___76_1856.FStar_Tactics_Types.entry_range)
                                                      }  in
                                                    let uu____1857 = set p'
                                                       in
                                                    bind uu____1857
                                                      (fun uu____1865  ->
                                                         ret (a, b))))))))))
  
let focus : 'a . 'a tac -> 'a tac =
  fun f  ->
    let uu____1883 = divide FStar_BigInt.one f idtac  in
    bind uu____1883
      (fun uu____1896  -> match uu____1896 with | (a,()) -> ret a)
  
let rec map : 'a . 'a tac -> 'a Prims.list tac =
  fun tau  ->
    bind get
      (fun p  ->
         match p.FStar_Tactics_Types.goals with
         | [] -> ret []
         | uu____1930::uu____1931 ->
             let uu____1934 =
               let uu____1943 = map tau  in
               divide FStar_BigInt.one tau uu____1943  in
             bind uu____1934
               (fun uu____1961  ->
                  match uu____1961 with | (h,t) -> ret (h :: t)))
  
let (seq : Prims.unit tac -> Prims.unit tac -> Prims.unit tac) =
  fun t1  ->
    fun t2  ->
      let uu____1998 =
        bind t1
          (fun uu____2003  ->
             let uu____2004 = map t2  in
             bind uu____2004 (fun uu____2012  -> ret ()))
         in
      focus uu____1998
  
let (intro : FStar_Syntax_Syntax.binder tac) =
  let uu____2019 =
    bind cur_goal
      (fun goal  ->
         let uu____2028 =
           FStar_Syntax_Util.arrow_one goal.FStar_Tactics_Types.goal_ty  in
         match uu____2028 with
         | FStar_Pervasives_Native.Some (b,c) ->
             let uu____2043 =
               let uu____2044 = FStar_Syntax_Util.is_total_comp c  in
               Prims.op_Negation uu____2044  in
             if uu____2043
             then fail "Codomain is effectful"
             else
               (let env' =
                  FStar_TypeChecker_Env.push_binders
                    goal.FStar_Tactics_Types.context [b]
                   in
                let typ' = comp_to_typ c  in
                let uu____2050 = new_uvar "intro" env' typ'  in
                bind uu____2050
                  (fun u  ->
                     let uu____2057 =
                       let uu____2058 =
                         FStar_Syntax_Util.abs [b] u
                           FStar_Pervasives_Native.None
                          in
                       trysolve goal uu____2058  in
                     if uu____2057
                     then
                       let uu____2061 =
                         let uu____2064 =
                           let uu___79_2065 = goal  in
                           let uu____2066 = bnorm env' u  in
                           let uu____2067 = bnorm env' typ'  in
                           {
                             FStar_Tactics_Types.context = env';
                             FStar_Tactics_Types.witness = uu____2066;
                             FStar_Tactics_Types.goal_ty = uu____2067;
                             FStar_Tactics_Types.opts =
                               (uu___79_2065.FStar_Tactics_Types.opts);
                             FStar_Tactics_Types.is_guard =
                               (uu___79_2065.FStar_Tactics_Types.is_guard)
                           }  in
                         replace_cur uu____2064  in
                       bind uu____2061 (fun uu____2069  -> ret b)
                     else fail "unification failed"))
         | FStar_Pervasives_Native.None  ->
             let uu____2075 =
               tts goal.FStar_Tactics_Types.context
                 goal.FStar_Tactics_Types.goal_ty
                in
             fail1 "goal is not an arrow (%s)" uu____2075)
     in
  FStar_All.pipe_left (wrap_err "intro") uu____2019 
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
       (let uu____2106 =
          FStar_Syntax_Util.arrow_one goal.FStar_Tactics_Types.goal_ty  in
        match uu____2106 with
        | FStar_Pervasives_Native.Some (b,c) ->
            let uu____2125 =
              let uu____2126 = FStar_Syntax_Util.is_total_comp c  in
              Prims.op_Negation uu____2126  in
            if uu____2125
            then fail "Codomain is effectful"
            else
              (let bv =
                 FStar_Syntax_Syntax.gen_bv "__recf"
                   FStar_Pervasives_Native.None
                   goal.FStar_Tactics_Types.goal_ty
                  in
               let bs =
                 let uu____2142 = FStar_Syntax_Syntax.mk_binder bv  in
                 [uu____2142; b]  in
               let env' =
                 FStar_TypeChecker_Env.push_binders
                   goal.FStar_Tactics_Types.context bs
                  in
               let uu____2144 =
                 let uu____2147 = comp_to_typ c  in
                 new_uvar "intro_rec" env' uu____2147  in
               bind uu____2144
                 (fun u  ->
                    let lb =
                      let uu____2163 =
                        FStar_Syntax_Util.abs [b] u
                          FStar_Pervasives_Native.None
                         in
                      FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl bv) []
                        goal.FStar_Tactics_Types.goal_ty
                        FStar_Parser_Const.effect_Tot_lid uu____2163 []
                        FStar_Range.dummyRange
                       in
                    let body = FStar_Syntax_Syntax.bv_to_name bv  in
                    let uu____2169 =
                      FStar_Syntax_Subst.close_let_rec [lb] body  in
                    match uu____2169 with
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
                          let uu____2206 =
                            let uu____2209 =
                              let uu___80_2210 = goal  in
                              let uu____2211 = bnorm env' u  in
                              let uu____2212 =
                                let uu____2213 = comp_to_typ c  in
                                bnorm env' uu____2213  in
                              {
                                FStar_Tactics_Types.context = env';
                                FStar_Tactics_Types.witness = uu____2211;
                                FStar_Tactics_Types.goal_ty = uu____2212;
                                FStar_Tactics_Types.opts =
                                  (uu___80_2210.FStar_Tactics_Types.opts);
                                FStar_Tactics_Types.is_guard =
                                  (uu___80_2210.FStar_Tactics_Types.is_guard)
                              }  in
                            replace_cur uu____2209  in
                          bind uu____2206
                            (fun uu____2220  ->
                               let uu____2221 =
                                 let uu____2226 =
                                   FStar_Syntax_Syntax.mk_binder bv  in
                                 (uu____2226, b)  in
                               ret uu____2221)
                        else fail "intro_rec: unification failed"))
        | FStar_Pervasives_Native.None  ->
            let uu____2240 =
              tts goal.FStar_Tactics_Types.context
                goal.FStar_Tactics_Types.goal_ty
               in
            fail1 "intro_rec: goal is not an arrow (%s)" uu____2240))
  
let (norm : FStar_Syntax_Embeddings.norm_step Prims.list -> Prims.unit tac) =
  fun s  ->
    bind cur_goal
      (fun goal  ->
         mlog
           (fun uu____2260  ->
              let uu____2261 =
                FStar_Syntax_Print.term_to_string
                  goal.FStar_Tactics_Types.witness
                 in
              FStar_Util.print1 "norm: witness = %s\n" uu____2261)
           (fun uu____2266  ->
              let steps =
                let uu____2270 = FStar_TypeChecker_Normalize.tr_norm_steps s
                   in
                FStar_List.append
                  [FStar_TypeChecker_Normalize.Reify;
                  FStar_TypeChecker_Normalize.UnfoldTac] uu____2270
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
                (let uu___81_2277 = goal  in
                 {
                   FStar_Tactics_Types.context =
                     (uu___81_2277.FStar_Tactics_Types.context);
                   FStar_Tactics_Types.witness = w;
                   FStar_Tactics_Types.goal_ty = t;
                   FStar_Tactics_Types.opts =
                     (uu___81_2277.FStar_Tactics_Types.opts);
                   FStar_Tactics_Types.is_guard =
                     (uu___81_2277.FStar_Tactics_Types.is_guard)
                 })))
  
let (norm_term_env :
  env ->
    FStar_Syntax_Embeddings.norm_step Prims.list ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac)
  =
  fun e  ->
    fun s  ->
      fun t  ->
        let uu____2295 =
          mlog
            (fun uu____2300  ->
               let uu____2301 = FStar_Syntax_Print.term_to_string t  in
               FStar_Util.print1 "norm_term: tm = %s\n" uu____2301)
            (fun uu____2303  ->
               bind get
                 (fun ps  ->
                    mlog
                      (fun uu____2308  ->
                         let uu____2309 =
                           tts ps.FStar_Tactics_Types.main_context t  in
                         FStar_Util.print1 "norm_term_env: t = %s\n"
                           uu____2309)
                      (fun uu____2312  ->
                         let uu____2313 = __tc e t  in
                         bind uu____2313
                           (fun uu____2335  ->
                              match uu____2335 with
                              | (t1,uu____2345,guard) ->
                                  (FStar_TypeChecker_Rel.force_trivial_guard
                                     e guard;
                                   (let steps =
                                      let uu____2351 =
                                        FStar_TypeChecker_Normalize.tr_norm_steps
                                          s
                                         in
                                      FStar_List.append
                                        [FStar_TypeChecker_Normalize.Reify;
                                        FStar_TypeChecker_Normalize.UnfoldTac]
                                        uu____2351
                                       in
                                    let t2 =
                                      normalize steps
                                        ps.FStar_Tactics_Types.main_context
                                        t1
                                       in
                                    ret t2))))))
           in
        FStar_All.pipe_left (wrap_err "norm_term") uu____2295
  
let (refine_intro : Prims.unit tac) =
  let uu____2363 =
    bind cur_goal
      (fun g  ->
         let uu____2370 =
           FStar_TypeChecker_Rel.base_and_refinement
             g.FStar_Tactics_Types.context g.FStar_Tactics_Types.goal_ty
            in
         match uu____2370 with
         | (uu____2383,FStar_Pervasives_Native.None ) ->
             fail "not a refinement"
         | (t,FStar_Pervasives_Native.Some (bv,phi)) ->
             let g1 =
               let uu___82_2408 = g  in
               {
                 FStar_Tactics_Types.context =
                   (uu___82_2408.FStar_Tactics_Types.context);
                 FStar_Tactics_Types.witness =
                   (uu___82_2408.FStar_Tactics_Types.witness);
                 FStar_Tactics_Types.goal_ty = t;
                 FStar_Tactics_Types.opts =
                   (uu___82_2408.FStar_Tactics_Types.opts);
                 FStar_Tactics_Types.is_guard =
                   (uu___82_2408.FStar_Tactics_Types.is_guard)
               }  in
             let uu____2409 =
               let uu____2414 =
                 let uu____2419 =
                   let uu____2420 = FStar_Syntax_Syntax.mk_binder bv  in
                   [uu____2420]  in
                 FStar_Syntax_Subst.open_term uu____2419 phi  in
               match uu____2414 with
               | (bvs,phi1) ->
                   let uu____2427 =
                     let uu____2428 = FStar_List.hd bvs  in
                     FStar_Pervasives_Native.fst uu____2428  in
                   (uu____2427, phi1)
                in
             (match uu____2409 with
              | (bv1,phi1) ->
                  let uu____2441 =
                    let uu____2444 =
                      FStar_Syntax_Subst.subst
                        [FStar_Syntax_Syntax.NT
                           (bv1, (g.FStar_Tactics_Types.witness))] phi1
                       in
                    mk_irrelevant_goal "refine_intro refinement"
                      g.FStar_Tactics_Types.context uu____2444
                      g.FStar_Tactics_Types.opts
                     in
                  bind uu____2441
                    (fun g2  ->
                       bind dismiss (fun uu____2448  -> add_goals [g1; g2]))))
     in
  FStar_All.pipe_left (wrap_err "refine_intro") uu____2363 
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
             let uu____2472 = __tc env t  in
             bind uu____2472
               (fun uu____2492  ->
                  match uu____2492 with
                  | (t1,typ,guard) ->
                      let uu____2504 =
                        if force_guard
                        then
                          must_trivial goal.FStar_Tactics_Types.context guard
                        else
                          add_goal_from_guard "__exact typing"
                            goal.FStar_Tactics_Types.context guard
                            goal.FStar_Tactics_Types.opts
                         in
                      bind uu____2504
                        (fun uu____2511  ->
                           mlog
                             (fun uu____2515  ->
                                let uu____2516 =
                                  tts goal.FStar_Tactics_Types.context typ
                                   in
                                let uu____2517 =
                                  tts goal.FStar_Tactics_Types.context
                                    goal.FStar_Tactics_Types.goal_ty
                                   in
                                FStar_Util.print2
                                  "exact: unifying %s and %s\n" uu____2516
                                  uu____2517)
                             (fun uu____2520  ->
                                let uu____2521 =
                                  do_unify goal.FStar_Tactics_Types.context
                                    typ goal.FStar_Tactics_Types.goal_ty
                                   in
                                if uu____2521
                                then solve goal t1
                                else
                                  (let uu____2525 =
                                     tts goal.FStar_Tactics_Types.context t1
                                      in
                                   let uu____2526 =
                                     tts goal.FStar_Tactics_Types.context typ
                                      in
                                   let uu____2527 =
                                     tts goal.FStar_Tactics_Types.context
                                       goal.FStar_Tactics_Types.goal_ty
                                      in
                                   let uu____2528 =
                                     tts goal.FStar_Tactics_Types.context
                                       goal.FStar_Tactics_Types.witness
                                      in
                                   fail4
                                     "%s : %s does not exactly solve the goal %s (witness = %s)"
                                     uu____2525 uu____2526 uu____2527
                                     uu____2528)))))
  
let (t_exact :
  Prims.bool -> Prims.bool -> FStar_Syntax_Syntax.term -> Prims.unit tac) =
  fun set_expected_typ1  ->
    fun force_guard  ->
      fun tm  ->
        let uu____2542 =
          mlog
            (fun uu____2547  ->
               let uu____2548 = FStar_Syntax_Print.term_to_string tm  in
               FStar_Util.print1 "t_exact: tm = %s\n" uu____2548)
            (fun uu____2551  ->
               let uu____2552 =
                 let uu____2559 =
                   __exact_now set_expected_typ1 force_guard tm  in
                 trytac' uu____2559  in
               bind uu____2552
                 (fun uu___56_2568  ->
                    match uu___56_2568 with
                    | FStar_Util.Inr r -> ret ()
                    | FStar_Util.Inl e ->
                        let uu____2577 =
                          let uu____2584 =
                            let uu____2587 =
                              norm [FStar_Syntax_Embeddings.Delta]  in
                            bind uu____2587
                              (fun uu____2591  ->
                                 bind refine_intro
                                   (fun uu____2593  ->
                                      __exact_now set_expected_typ1
                                        force_guard tm))
                             in
                          trytac' uu____2584  in
                        bind uu____2577
                          (fun uu___55_2600  ->
                             match uu___55_2600 with
                             | FStar_Util.Inr r -> ret ()
                             | FStar_Util.Inl uu____2608 -> fail e)))
           in
        FStar_All.pipe_left (wrap_err "exact") uu____2542
  
let (uvar_free_in_goal :
  FStar_Syntax_Syntax.uvar -> FStar_Tactics_Types.goal -> Prims.bool) =
  fun u  ->
    fun g  ->
      if g.FStar_Tactics_Types.is_guard
      then false
      else
        (let free_uvars =
           let uu____2623 =
             let uu____2630 =
               FStar_Syntax_Free.uvars g.FStar_Tactics_Types.goal_ty  in
             FStar_Util.set_elements uu____2630  in
           FStar_List.map FStar_Pervasives_Native.fst uu____2623  in
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
          let uu____2690 = f x  in
          bind uu____2690
            (fun y  ->
               let uu____2698 = mapM f xs  in
               bind uu____2698 (fun ys  -> ret (y :: ys)))
  
exception NoUnif 
let (uu___is_NoUnif : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with | NoUnif  -> true | uu____2716 -> false
  
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
               (fun uu____2734  ->
                  let uu____2735 = FStar_Syntax_Print.term_to_string tm  in
                  FStar_Util.print1 ">>> Calling __exact(%s)\n" uu____2735)
               (fun uu____2738  ->
                  let uu____2739 =
                    let uu____2744 = t_exact false true tm  in
                    trytac uu____2744  in
                  bind uu____2739
                    (fun uu___57_2751  ->
                       match uu___57_2751 with
                       | FStar_Pervasives_Native.Some r -> ret ()
                       | FStar_Pervasives_Native.None  ->
                           mlog
                             (fun uu____2759  ->
                                let uu____2760 =
                                  FStar_Syntax_Print.term_to_string typ  in
                                FStar_Util.print1 ">>> typ = %s\n" uu____2760)
                             (fun uu____2763  ->
                                let uu____2764 =
                                  FStar_Syntax_Util.arrow_one typ  in
                                match uu____2764 with
                                | FStar_Pervasives_Native.None  ->
                                    FStar_Exn.raise NoUnif
                                | FStar_Pervasives_Native.Some ((bv,aq),c) ->
                                    mlog
                                      (fun uu____2796  ->
                                         let uu____2797 =
                                           FStar_Syntax_Print.binder_to_string
                                             (bv, aq)
                                            in
                                         FStar_Util.print1
                                           "__apply: pushing binder %s\n"
                                           uu____2797)
                                      (fun uu____2800  ->
                                         let uu____2801 =
                                           let uu____2802 =
                                             FStar_Syntax_Util.is_total_comp
                                               c
                                              in
                                           Prims.op_Negation uu____2802  in
                                         if uu____2801
                                         then
                                           fail "apply: not total codomain"
                                         else
                                           (let uu____2806 =
                                              new_uvar "apply"
                                                goal.FStar_Tactics_Types.context
                                                bv.FStar_Syntax_Syntax.sort
                                               in
                                            bind uu____2806
                                              (fun u  ->
                                                 let tm' =
                                                   FStar_Syntax_Syntax.mk_Tm_app
                                                     tm [(u, aq)]
                                                     FStar_Pervasives_Native.None
                                                     tm.FStar_Syntax_Syntax.pos
                                                    in
                                                 let typ' =
                                                   let uu____2826 =
                                                     comp_to_typ c  in
                                                   FStar_All.pipe_left
                                                     (FStar_Syntax_Subst.subst
                                                        [FStar_Syntax_Syntax.NT
                                                           (bv, u)])
                                                     uu____2826
                                                    in
                                                 let uu____2827 =
                                                   __apply uopt tm' typ'  in
                                                 bind uu____2827
                                                   (fun uu____2835  ->
                                                      let u1 =
                                                        bnorm
                                                          goal.FStar_Tactics_Types.context
                                                          u
                                                         in
                                                      let uu____2837 =
                                                        let uu____2838 =
                                                          let uu____2841 =
                                                            let uu____2842 =
                                                              FStar_Syntax_Util.head_and_args
                                                                u1
                                                               in
                                                            FStar_Pervasives_Native.fst
                                                              uu____2842
                                                             in
                                                          FStar_Syntax_Subst.compress
                                                            uu____2841
                                                           in
                                                        uu____2838.FStar_Syntax_Syntax.n
                                                         in
                                                      match uu____2837 with
                                                      | FStar_Syntax_Syntax.Tm_uvar
                                                          (uvar,uu____2870)
                                                          ->
                                                          bind get
                                                            (fun ps  ->
                                                               let uu____2898
                                                                 =
                                                                 uopt &&
                                                                   (uvar_free
                                                                    uvar ps)
                                                                  in
                                                               if uu____2898
                                                               then ret ()
                                                               else
                                                                 (let uu____2902
                                                                    =
                                                                    let uu____2905
                                                                    =
                                                                    let uu___83_2906
                                                                    = goal
                                                                     in
                                                                    let uu____2907
                                                                    =
                                                                    bnorm
                                                                    goal.FStar_Tactics_Types.context
                                                                    u1  in
                                                                    let uu____2908
                                                                    =
                                                                    bnorm
                                                                    goal.FStar_Tactics_Types.context
                                                                    bv.FStar_Syntax_Syntax.sort
                                                                     in
                                                                    {
                                                                    FStar_Tactics_Types.context
                                                                    =
                                                                    (uu___83_2906.FStar_Tactics_Types.context);
                                                                    FStar_Tactics_Types.witness
                                                                    =
                                                                    uu____2907;
                                                                    FStar_Tactics_Types.goal_ty
                                                                    =
                                                                    uu____2908;
                                                                    FStar_Tactics_Types.opts
                                                                    =
                                                                    (uu___83_2906.FStar_Tactics_Types.opts);
                                                                    FStar_Tactics_Types.is_guard
                                                                    = false
                                                                    }  in
                                                                    [uu____2905]
                                                                     in
                                                                  add_goals
                                                                    uu____2902))
                                                      | t -> ret ()))))))))
  
let try_unif : 'a . 'a tac -> 'a tac -> 'a tac =
  fun t  ->
    fun t'  -> mk_tac (fun ps  -> try run t ps with | NoUnif  -> run t' ps)
  
let (apply : Prims.bool -> FStar_Syntax_Syntax.term -> Prims.unit tac) =
  fun uopt  ->
    fun tm  ->
      let uu____2954 =
        mlog
          (fun uu____2959  ->
             let uu____2960 = FStar_Syntax_Print.term_to_string tm  in
             FStar_Util.print1 "apply: tm = %s\n" uu____2960)
          (fun uu____2962  ->
             bind cur_goal
               (fun goal  ->
                  let uu____2966 = __tc goal.FStar_Tactics_Types.context tm
                     in
                  bind uu____2966
                    (fun uu____2987  ->
                       match uu____2987 with
                       | (tm1,typ,guard) ->
                           let uu____2999 =
                             let uu____3002 =
                               let uu____3005 = __apply uopt tm1 typ  in
                               bind uu____3005
                                 (fun uu____3009  ->
                                    add_goal_from_guard "apply guard"
                                      goal.FStar_Tactics_Types.context guard
                                      goal.FStar_Tactics_Types.opts)
                                in
                             focus uu____3002  in
                           let uu____3010 =
                             let uu____3013 =
                               tts goal.FStar_Tactics_Types.context tm1  in
                             let uu____3014 =
                               tts goal.FStar_Tactics_Types.context typ  in
                             let uu____3015 =
                               tts goal.FStar_Tactics_Types.context
                                 goal.FStar_Tactics_Types.goal_ty
                                in
                             fail3
                               "Cannot instantiate %s (of type %s) to match goal (%s)"
                               uu____3013 uu____3014 uu____3015
                              in
                           try_unif uu____2999 uu____3010)))
         in
      FStar_All.pipe_left (wrap_err "apply") uu____2954
  
let (apply_lemma : FStar_Syntax_Syntax.term -> Prims.unit tac) =
  fun tm  ->
    let uu____3027 =
      let uu____3030 =
        mlog
          (fun uu____3035  ->
             let uu____3036 = FStar_Syntax_Print.term_to_string tm  in
             FStar_Util.print1 "apply_lemma: tm = %s\n" uu____3036)
          (fun uu____3039  ->
             let is_unit_t t =
               let uu____3044 =
                 let uu____3045 = FStar_Syntax_Subst.compress t  in
                 uu____3045.FStar_Syntax_Syntax.n  in
               match uu____3044 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.unit_lid
                   -> true
               | uu____3049 -> false  in
             bind cur_goal
               (fun goal  ->
                  let uu____3053 = __tc goal.FStar_Tactics_Types.context tm
                     in
                  bind uu____3053
                    (fun uu____3075  ->
                       match uu____3075 with
                       | (tm1,t,guard) ->
                           let uu____3087 =
                             FStar_Syntax_Util.arrow_formals_comp t  in
                           (match uu____3087 with
                            | (bs,comp) ->
                                if
                                  Prims.op_Negation
                                    (FStar_Syntax_Util.is_lemma_comp comp)
                                then fail "not a lemma"
                                else
                                  (let uu____3117 =
                                     FStar_List.fold_left
                                       (fun uu____3163  ->
                                          fun uu____3164  ->
                                            match (uu____3163, uu____3164)
                                            with
                                            | ((uvs,guard1,subst1),(b,aq)) ->
                                                let b_t =
                                                  FStar_Syntax_Subst.subst
                                                    subst1
                                                    b.FStar_Syntax_Syntax.sort
                                                   in
                                                let uu____3267 =
                                                  is_unit_t b_t  in
                                                if uu____3267
                                                then
                                                  (((FStar_Syntax_Util.exp_unit,
                                                      aq) :: uvs), guard1,
                                                    ((FStar_Syntax_Syntax.NT
                                                        (b,
                                                          FStar_Syntax_Util.exp_unit))
                                                    :: subst1))
                                                else
                                                  (let uu____3305 =
                                                     FStar_TypeChecker_Util.new_implicit_var
                                                       "apply_lemma"
                                                       (goal.FStar_Tactics_Types.goal_ty).FStar_Syntax_Syntax.pos
                                                       goal.FStar_Tactics_Types.context
                                                       b_t
                                                      in
                                                   match uu____3305 with
                                                   | (u,uu____3335,g_u) ->
                                                       let uu____3349 =
                                                         FStar_TypeChecker_Rel.conj_guard
                                                           guard1 g_u
                                                          in
                                                       (((u, aq) :: uvs),
                                                         uu____3349,
                                                         ((FStar_Syntax_Syntax.NT
                                                             (b, u)) ::
                                                         subst1))))
                                       ([], guard, []) bs
                                      in
                                   match uu____3117 with
                                   | (uvs,implicits,subst1) ->
                                       let uvs1 = FStar_List.rev uvs  in
                                       let comp1 =
                                         FStar_Syntax_Subst.subst_comp subst1
                                           comp
                                          in
                                       let uu____3419 =
                                         let uu____3428 =
                                           let uu____3437 =
                                             FStar_Syntax_Util.comp_to_comp_typ
                                               comp1
                                              in
                                           uu____3437.FStar_Syntax_Syntax.effect_args
                                            in
                                         match uu____3428 with
                                         | pre::post::uu____3448 ->
                                             ((FStar_Pervasives_Native.fst
                                                 pre),
                                               (FStar_Pervasives_Native.fst
                                                  post))
                                         | uu____3489 ->
                                             failwith
                                               "apply_lemma: impossible: not a lemma"
                                          in
                                       (match uu____3419 with
                                        | (pre,post) ->
                                            let post1 =
                                              let uu____3521 =
                                                let uu____3530 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    FStar_Syntax_Util.exp_unit
                                                   in
                                                [uu____3530]  in
                                              FStar_Syntax_Util.mk_app post
                                                uu____3521
                                               in
                                            let uu____3531 =
                                              let uu____3532 =
                                                let uu____3533 =
                                                  FStar_Syntax_Util.mk_squash
                                                    FStar_Syntax_Syntax.U_zero
                                                    post1
                                                   in
                                                do_unify
                                                  goal.FStar_Tactics_Types.context
                                                  uu____3533
                                                  goal.FStar_Tactics_Types.goal_ty
                                                 in
                                              Prims.op_Negation uu____3532
                                               in
                                            if uu____3531
                                            then
                                              let uu____3536 =
                                                tts
                                                  goal.FStar_Tactics_Types.context
                                                  tm1
                                                 in
                                              let uu____3537 =
                                                let uu____3538 =
                                                  FStar_Syntax_Util.mk_squash
                                                    FStar_Syntax_Syntax.U_zero
                                                    post1
                                                   in
                                                tts
                                                  goal.FStar_Tactics_Types.context
                                                  uu____3538
                                                 in
                                              let uu____3539 =
                                                tts
                                                  goal.FStar_Tactics_Types.context
                                                  goal.FStar_Tactics_Types.goal_ty
                                                 in
                                              fail3
                                                "Cannot instantiate lemma %s (with postcondition: %s) to match goal (%s)"
                                                uu____3536 uu____3537
                                                uu____3539
                                            else
                                              (let uu____3541 =
                                                 add_implicits
                                                   implicits.FStar_TypeChecker_Env.implicits
                                                  in
                                               bind uu____3541
                                                 (fun uu____3546  ->
                                                    let uu____3547 =
                                                      solve goal
                                                        FStar_Syntax_Util.exp_unit
                                                       in
                                                    bind uu____3547
                                                      (fun uu____3555  ->
                                                         let is_free_uvar uv
                                                           t1 =
                                                           let free_uvars =
                                                             let uu____3566 =
                                                               let uu____3573
                                                                 =
                                                                 FStar_Syntax_Free.uvars
                                                                   t1
                                                                  in
                                                               FStar_Util.set_elements
                                                                 uu____3573
                                                                in
                                                             FStar_List.map
                                                               FStar_Pervasives_Native.fst
                                                               uu____3566
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
                                                           let uu____3614 =
                                                             FStar_Syntax_Util.head_and_args
                                                               t1
                                                              in
                                                           match uu____3614
                                                           with
                                                           | (hd1,uu____3630)
                                                               ->
                                                               (match 
                                                                  hd1.FStar_Syntax_Syntax.n
                                                                with
                                                                | FStar_Syntax_Syntax.Tm_uvar
                                                                    (uv,uu____3652)
                                                                    ->
                                                                    appears
                                                                    uv goals
                                                                | uu____3677
                                                                    -> false)
                                                            in
                                                         let uu____3678 =
                                                           FStar_All.pipe_right
                                                             implicits.FStar_TypeChecker_Env.implicits
                                                             (mapM
                                                                (fun
                                                                   uu____3750
                                                                    ->
                                                                   match uu____3750
                                                                   with
                                                                   | 
                                                                   (_msg,env,_uvar,term,typ,uu____3778)
                                                                    ->
                                                                    let uu____3779
                                                                    =
                                                                    FStar_Syntax_Util.head_and_args
                                                                    term  in
                                                                    (match uu____3779
                                                                    with
                                                                    | 
                                                                    (hd1,uu____3805)
                                                                    ->
                                                                    let uu____3826
                                                                    =
                                                                    let uu____3827
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    hd1  in
                                                                    uu____3827.FStar_Syntax_Syntax.n
                                                                     in
                                                                    (match uu____3826
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Tm_uvar
                                                                    uu____3840
                                                                    ->
                                                                    let uu____3857
                                                                    =
                                                                    let uu____3866
                                                                    =
                                                                    let uu____3869
                                                                    =
                                                                    let uu___86_3870
                                                                    = goal
                                                                     in
                                                                    let uu____3871
                                                                    =
                                                                    bnorm
                                                                    goal.FStar_Tactics_Types.context
                                                                    term  in
                                                                    let uu____3872
                                                                    =
                                                                    bnorm
                                                                    goal.FStar_Tactics_Types.context
                                                                    typ  in
                                                                    {
                                                                    FStar_Tactics_Types.context
                                                                    =
                                                                    (uu___86_3870.FStar_Tactics_Types.context);
                                                                    FStar_Tactics_Types.witness
                                                                    =
                                                                    uu____3871;
                                                                    FStar_Tactics_Types.goal_ty
                                                                    =
                                                                    uu____3872;
                                                                    FStar_Tactics_Types.opts
                                                                    =
                                                                    (uu___86_3870.FStar_Tactics_Types.opts);
                                                                    FStar_Tactics_Types.is_guard
                                                                    =
                                                                    (uu___86_3870.FStar_Tactics_Types.is_guard)
                                                                    }  in
                                                                    [uu____3869]
                                                                     in
                                                                    (uu____3866,
                                                                    [])  in
                                                                    ret
                                                                    uu____3857
                                                                    | 
                                                                    uu____3885
                                                                    ->
                                                                    let g_typ
                                                                    =
                                                                    let uu____3887
                                                                    =
                                                                    FStar_Options.__temp_fast_implicits
                                                                    ()  in
                                                                    if
                                                                    uu____3887
                                                                    then
                                                                    FStar_TypeChecker_TcTerm.check_type_of_well_typed_term
                                                                    false env
                                                                    term typ
                                                                    else
                                                                    (let term1
                                                                    =
                                                                    bnorm env
                                                                    term  in
                                                                    let uu____3890
                                                                    =
                                                                    let uu____3897
                                                                    =
                                                                    FStar_TypeChecker_Env.set_expected_typ
                                                                    env typ
                                                                     in
                                                                    env.FStar_TypeChecker_Env.type_of
                                                                    uu____3897
                                                                    term1  in
                                                                    match uu____3890
                                                                    with
                                                                    | 
                                                                    (uu____3898,uu____3899,g_typ)
                                                                    -> g_typ)
                                                                     in
                                                                    let uu____3901
                                                                    =
                                                                    goal_from_guard
                                                                    "apply_lemma solved arg"
                                                                    goal.FStar_Tactics_Types.context
                                                                    g_typ
                                                                    goal.FStar_Tactics_Types.opts
                                                                     in
                                                                    bind
                                                                    uu____3901
                                                                    (fun
                                                                    uu___58_3917
                                                                     ->
                                                                    match uu___58_3917
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
                                                         bind uu____3678
                                                           (fun goals_  ->
                                                              let sub_goals =
                                                                let uu____3985
                                                                  =
                                                                  FStar_List.map
                                                                    FStar_Pervasives_Native.fst
                                                                    goals_
                                                                   in
                                                                FStar_List.flatten
                                                                  uu____3985
                                                                 in
                                                              let smt_goals =
                                                                let uu____4007
                                                                  =
                                                                  FStar_List.map
                                                                    FStar_Pervasives_Native.snd
                                                                    goals_
                                                                   in
                                                                FStar_List.flatten
                                                                  uu____4007
                                                                 in
                                                              let rec filter'
                                                                a f xs =
                                                                match xs with
                                                                | [] -> []
                                                                | x::xs1 ->
                                                                    let uu____4062
                                                                    = f x xs1
                                                                     in
                                                                    if
                                                                    uu____4062
                                                                    then
                                                                    let uu____4065
                                                                    =
                                                                    filter'
                                                                    () f xs1
                                                                     in x ::
                                                                    uu____4065
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
                                                                    let uu____4079
                                                                    =
                                                                    checkone
                                                                    g.FStar_Tactics_Types.witness
                                                                    goals  in
                                                                    Prims.op_Negation
                                                                    uu____4079))
                                                                    a438 a439)
                                                                    (Obj.magic
                                                                    sub_goals))
                                                                 in
                                                              let uu____4080
                                                                =
                                                                add_goal_from_guard
                                                                  "apply_lemma guard"
                                                                  goal.FStar_Tactics_Types.context
                                                                  guard
                                                                  goal.FStar_Tactics_Types.opts
                                                                 in
                                                              bind uu____4080
                                                                (fun
                                                                   uu____4085
                                                                    ->
                                                                   let uu____4086
                                                                    =
                                                                    let uu____4089
                                                                    =
                                                                    let uu____4090
                                                                    =
                                                                    let uu____4091
                                                                    =
                                                                    FStar_Syntax_Util.mk_squash
                                                                    FStar_Syntax_Syntax.U_zero
                                                                    pre  in
                                                                    istrivial
                                                                    goal.FStar_Tactics_Types.context
                                                                    uu____4091
                                                                     in
                                                                    Prims.op_Negation
                                                                    uu____4090
                                                                     in
                                                                    if
                                                                    uu____4089
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
                                                                    uu____4086
                                                                    (fun
                                                                    uu____4097
                                                                     ->
                                                                    let uu____4098
                                                                    =
                                                                    add_smt_goals
                                                                    smt_goals
                                                                     in
                                                                    bind
                                                                    uu____4098
                                                                    (fun
                                                                    uu____4102
                                                                     ->
                                                                    add_goals
                                                                    sub_goals1)))))))))))))
         in
      focus uu____3030  in
    FStar_All.pipe_left (wrap_err "apply_lemma") uu____3027
  
let (destruct_eq' :
  FStar_Syntax_Syntax.typ ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun typ  ->
    let uu____4122 = FStar_Syntax_Util.destruct_typ_as_formula typ  in
    match uu____4122 with
    | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn
        (l,uu____4132::(e1,uu____4134)::(e2,uu____4136)::[])) when
        FStar_Ident.lid_equals l FStar_Parser_Const.eq2_lid ->
        FStar_Pervasives_Native.Some (e1, e2)
    | uu____4195 -> FStar_Pervasives_Native.None
  
let (destruct_eq :
  FStar_Syntax_Syntax.typ ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun typ  ->
    let uu____4217 = destruct_eq' typ  in
    match uu____4217 with
    | FStar_Pervasives_Native.Some t -> FStar_Pervasives_Native.Some t
    | FStar_Pervasives_Native.None  ->
        let uu____4247 = FStar_Syntax_Util.un_squash typ  in
        (match uu____4247 with
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
        let uu____4303 = FStar_TypeChecker_Env.pop_bv e1  in
        match uu____4303 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (bv',e') ->
            if FStar_Syntax_Syntax.bv_eq bvar bv'
            then FStar_Pervasives_Native.Some (e', [])
            else
              (let uu____4351 = aux e'  in
               FStar_Util.map_opt uu____4351
                 (fun uu____4375  ->
                    match uu____4375 with | (e'',bvs) -> (e'', (bv' :: bvs))))
         in
      let uu____4396 = aux e  in
      FStar_Util.map_opt uu____4396
        (fun uu____4420  ->
           match uu____4420 with | (e',bvs) -> (e', (FStar_List.rev bvs)))
  
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
          let uu____4475 = split_env b1 g.FStar_Tactics_Types.context  in
          FStar_Util.map_opt uu____4475
            (fun uu____4499  ->
               match uu____4499 with
               | (e0,bvs) ->
                   let s1 bv =
                     let uu___87_4516 = bv  in
                     let uu____4517 =
                       FStar_Syntax_Subst.subst s bv.FStar_Syntax_Syntax.sort
                        in
                     {
                       FStar_Syntax_Syntax.ppname =
                         (uu___87_4516.FStar_Syntax_Syntax.ppname);
                       FStar_Syntax_Syntax.index =
                         (uu___87_4516.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort = uu____4517
                     }  in
                   let bvs1 = FStar_List.map s1 bvs  in
                   let c = push_bvs e0 (b2 :: bvs1)  in
                   let w =
                     FStar_Syntax_Subst.subst s g.FStar_Tactics_Types.witness
                      in
                   let t =
                     FStar_Syntax_Subst.subst s g.FStar_Tactics_Types.goal_ty
                      in
                   let uu___88_4526 = g  in
                   {
                     FStar_Tactics_Types.context = c;
                     FStar_Tactics_Types.witness = w;
                     FStar_Tactics_Types.goal_ty = t;
                     FStar_Tactics_Types.opts =
                       (uu___88_4526.FStar_Tactics_Types.opts);
                     FStar_Tactics_Types.is_guard =
                       (uu___88_4526.FStar_Tactics_Types.is_guard)
                   })
  
let (rewrite : FStar_Syntax_Syntax.binder -> Prims.unit tac) =
  fun h  ->
    bind cur_goal
      (fun goal  ->
         let uu____4539 = h  in
         match uu____4539 with
         | (bv,uu____4543) ->
             mlog
               (fun uu____4547  ->
                  let uu____4548 = FStar_Syntax_Print.bv_to_string bv  in
                  let uu____4549 =
                    tts goal.FStar_Tactics_Types.context
                      bv.FStar_Syntax_Syntax.sort
                     in
                  FStar_Util.print2 "+++Rewrite %s : %s\n" uu____4548
                    uu____4549)
               (fun uu____4552  ->
                  let uu____4553 =
                    split_env bv goal.FStar_Tactics_Types.context  in
                  match uu____4553 with
                  | FStar_Pervasives_Native.None  ->
                      fail "rewrite: binder not found in environment"
                  | FStar_Pervasives_Native.Some (e0,bvs) ->
                      let uu____4582 =
                        destruct_eq bv.FStar_Syntax_Syntax.sort  in
                      (match uu____4582 with
                       | FStar_Pervasives_Native.Some (x,e) ->
                           let uu____4597 =
                             let uu____4598 = FStar_Syntax_Subst.compress x
                                in
                             uu____4598.FStar_Syntax_Syntax.n  in
                           (match uu____4597 with
                            | FStar_Syntax_Syntax.Tm_name x1 ->
                                let s = [FStar_Syntax_Syntax.NT (x1, e)]  in
                                let s1 bv1 =
                                  let uu___89_4611 = bv1  in
                                  let uu____4612 =
                                    FStar_Syntax_Subst.subst s
                                      bv1.FStar_Syntax_Syntax.sort
                                     in
                                  {
                                    FStar_Syntax_Syntax.ppname =
                                      (uu___89_4611.FStar_Syntax_Syntax.ppname);
                                    FStar_Syntax_Syntax.index =
                                      (uu___89_4611.FStar_Syntax_Syntax.index);
                                    FStar_Syntax_Syntax.sort = uu____4612
                                  }  in
                                let bvs1 = FStar_List.map s1 bvs  in
                                let uu____4618 =
                                  let uu___90_4619 = goal  in
                                  let uu____4620 = push_bvs e0 (bv :: bvs1)
                                     in
                                  let uu____4621 =
                                    FStar_Syntax_Subst.subst s
                                      goal.FStar_Tactics_Types.witness
                                     in
                                  let uu____4622 =
                                    FStar_Syntax_Subst.subst s
                                      goal.FStar_Tactics_Types.goal_ty
                                     in
                                  {
                                    FStar_Tactics_Types.context = uu____4620;
                                    FStar_Tactics_Types.witness = uu____4621;
                                    FStar_Tactics_Types.goal_ty = uu____4622;
                                    FStar_Tactics_Types.opts =
                                      (uu___90_4619.FStar_Tactics_Types.opts);
                                    FStar_Tactics_Types.is_guard =
                                      (uu___90_4619.FStar_Tactics_Types.is_guard)
                                  }  in
                                replace_cur uu____4618
                            | uu____4623 ->
                                fail
                                  "rewrite: Not an equality hypothesis with a variable on the LHS")
                       | uu____4624 ->
                           fail "rewrite: Not an equality hypothesis")))
  
let (rename_to :
  FStar_Syntax_Syntax.binder -> Prims.string -> Prims.unit tac) =
  fun b  ->
    fun s  ->
      bind cur_goal
        (fun goal  ->
           let uu____4649 = b  in
           match uu____4649 with
           | (bv,uu____4653) ->
               let bv' =
                 FStar_Syntax_Syntax.freshen_bv
                   (let uu___91_4657 = bv  in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (FStar_Ident.mk_ident
                           (s,
                             ((bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange)));
                      FStar_Syntax_Syntax.index =
                        (uu___91_4657.FStar_Syntax_Syntax.index);
                      FStar_Syntax_Syntax.sort =
                        (uu___91_4657.FStar_Syntax_Syntax.sort)
                    })
                  in
               let s1 =
                 let uu____4661 =
                   let uu____4662 =
                     let uu____4669 = FStar_Syntax_Syntax.bv_to_name bv'  in
                     (bv, uu____4669)  in
                   FStar_Syntax_Syntax.NT uu____4662  in
                 [uu____4661]  in
               let uu____4670 = subst_goal bv bv' s1 goal  in
               (match uu____4670 with
                | FStar_Pervasives_Native.None  ->
                    fail "rename_to: binder not found in environment"
                | FStar_Pervasives_Native.Some goal1 -> replace_cur goal1))
  
let (binder_retype : FStar_Syntax_Syntax.binder -> Prims.unit tac) =
  fun b  ->
    bind cur_goal
      (fun goal  ->
         let uu____4689 = b  in
         match uu____4689 with
         | (bv,uu____4693) ->
             let uu____4694 = split_env bv goal.FStar_Tactics_Types.context
                in
             (match uu____4694 with
              | FStar_Pervasives_Native.None  ->
                  fail "binder_retype: binder is not present in environment"
              | FStar_Pervasives_Native.Some (e0,bvs) ->
                  let uu____4723 = FStar_Syntax_Util.type_u ()  in
                  (match uu____4723 with
                   | (ty,u) ->
                       let uu____4732 = new_uvar "binder_retype" e0 ty  in
                       bind uu____4732
                         (fun t'  ->
                            let bv'' =
                              let uu___92_4742 = bv  in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___92_4742.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___92_4742.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = t'
                              }  in
                            let s =
                              let uu____4746 =
                                let uu____4747 =
                                  let uu____4754 =
                                    FStar_Syntax_Syntax.bv_to_name bv''  in
                                  (bv, uu____4754)  in
                                FStar_Syntax_Syntax.NT uu____4747  in
                              [uu____4746]  in
                            let bvs1 =
                              FStar_List.map
                                (fun b1  ->
                                   let uu___93_4762 = b1  in
                                   let uu____4763 =
                                     FStar_Syntax_Subst.subst s
                                       b1.FStar_Syntax_Syntax.sort
                                      in
                                   {
                                     FStar_Syntax_Syntax.ppname =
                                       (uu___93_4762.FStar_Syntax_Syntax.ppname);
                                     FStar_Syntax_Syntax.index =
                                       (uu___93_4762.FStar_Syntax_Syntax.index);
                                     FStar_Syntax_Syntax.sort = uu____4763
                                   }) bvs
                               in
                            let env' = push_bvs e0 (bv'' :: bvs1)  in
                            bind dismiss
                              (fun uu____4769  ->
                                 let uu____4770 =
                                   let uu____4773 =
                                     let uu____4776 =
                                       let uu___94_4777 = goal  in
                                       let uu____4778 =
                                         FStar_Syntax_Subst.subst s
                                           goal.FStar_Tactics_Types.witness
                                          in
                                       let uu____4779 =
                                         FStar_Syntax_Subst.subst s
                                           goal.FStar_Tactics_Types.goal_ty
                                          in
                                       {
                                         FStar_Tactics_Types.context = env';
                                         FStar_Tactics_Types.witness =
                                           uu____4778;
                                         FStar_Tactics_Types.goal_ty =
                                           uu____4779;
                                         FStar_Tactics_Types.opts =
                                           (uu___94_4777.FStar_Tactics_Types.opts);
                                         FStar_Tactics_Types.is_guard =
                                           (uu___94_4777.FStar_Tactics_Types.is_guard)
                                       }  in
                                     [uu____4776]  in
                                   add_goals uu____4773  in
                                 bind uu____4770
                                   (fun uu____4782  ->
                                      let uu____4783 =
                                        FStar_Syntax_Util.mk_eq2
                                          (FStar_Syntax_Syntax.U_succ u) ty
                                          bv.FStar_Syntax_Syntax.sort t'
                                         in
                                      add_irrelevant_goal
                                        "binder_retype equation" e0
                                        uu____4783
                                        goal.FStar_Tactics_Types.opts))))))
  
let (norm_binder_type :
  FStar_Syntax_Embeddings.norm_step Prims.list ->
    FStar_Syntax_Syntax.binder -> Prims.unit tac)
  =
  fun s  ->
    fun b  ->
      bind cur_goal
        (fun goal  ->
           let uu____4804 = b  in
           match uu____4804 with
           | (bv,uu____4808) ->
               let uu____4809 = split_env bv goal.FStar_Tactics_Types.context
                  in
               (match uu____4809 with
                | FStar_Pervasives_Native.None  ->
                    fail
                      "binder_retype: binder is not present in environment"
                | FStar_Pervasives_Native.Some (e0,bvs) ->
                    let steps =
                      let uu____4841 =
                        FStar_TypeChecker_Normalize.tr_norm_steps s  in
                      FStar_List.append
                        [FStar_TypeChecker_Normalize.Reify;
                        FStar_TypeChecker_Normalize.UnfoldTac] uu____4841
                       in
                    let sort' =
                      normalize steps e0 bv.FStar_Syntax_Syntax.sort  in
                    let bv' =
                      let uu___95_4846 = bv  in
                      {
                        FStar_Syntax_Syntax.ppname =
                          (uu___95_4846.FStar_Syntax_Syntax.ppname);
                        FStar_Syntax_Syntax.index =
                          (uu___95_4846.FStar_Syntax_Syntax.index);
                        FStar_Syntax_Syntax.sort = sort'
                      }  in
                    let env' = push_bvs e0 (bv' :: bvs)  in
                    replace_cur
                      (let uu___96_4850 = goal  in
                       {
                         FStar_Tactics_Types.context = env';
                         FStar_Tactics_Types.witness =
                           (uu___96_4850.FStar_Tactics_Types.witness);
                         FStar_Tactics_Types.goal_ty =
                           (uu___96_4850.FStar_Tactics_Types.goal_ty);
                         FStar_Tactics_Types.opts =
                           (uu___96_4850.FStar_Tactics_Types.opts);
                         FStar_Tactics_Types.is_guard =
                           (uu___96_4850.FStar_Tactics_Types.is_guard)
                       })))
  
let (revert : Prims.unit tac) =
  bind cur_goal
    (fun goal  ->
       let uu____4858 =
         FStar_TypeChecker_Env.pop_bv goal.FStar_Tactics_Types.context  in
       match uu____4858 with
       | FStar_Pervasives_Native.None  -> fail "Cannot revert; empty context"
       | FStar_Pervasives_Native.Some (x,env') ->
           let typ' =
             let uu____4880 =
               FStar_Syntax_Syntax.mk_Total goal.FStar_Tactics_Types.goal_ty
                in
             FStar_Syntax_Util.arrow [(x, FStar_Pervasives_Native.None)]
               uu____4880
              in
           let w' =
             FStar_Syntax_Util.abs [(x, FStar_Pervasives_Native.None)]
               goal.FStar_Tactics_Types.witness FStar_Pervasives_Native.None
              in
           replace_cur
             (let uu___97_4914 = goal  in
              {
                FStar_Tactics_Types.context = env';
                FStar_Tactics_Types.witness = w';
                FStar_Tactics_Types.goal_ty = typ';
                FStar_Tactics_Types.opts =
                  (uu___97_4914.FStar_Tactics_Types.opts);
                FStar_Tactics_Types.is_guard =
                  (uu___97_4914.FStar_Tactics_Types.is_guard)
              }))
  
let (free_in :
  FStar_Syntax_Syntax.bv -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun bv  ->
    fun t  ->
      let uu____4921 = FStar_Syntax_Free.names t  in
      FStar_Util.set_mem bv uu____4921
  
let rec (clear : FStar_Syntax_Syntax.binder -> Prims.unit tac) =
  fun b  ->
    let bv = FStar_Pervasives_Native.fst b  in
    bind cur_goal
      (fun goal  ->
         mlog
           (fun uu____4937  ->
              let uu____4938 = FStar_Syntax_Print.binder_to_string b  in
              let uu____4939 =
                let uu____4940 =
                  let uu____4941 =
                    FStar_TypeChecker_Env.all_binders
                      goal.FStar_Tactics_Types.context
                     in
                  FStar_All.pipe_right uu____4941 FStar_List.length  in
                FStar_All.pipe_right uu____4940 FStar_Util.string_of_int  in
              FStar_Util.print2 "Clear of (%s), env has %s binders\n"
                uu____4938 uu____4939)
           (fun uu____4952  ->
              let uu____4953 = split_env bv goal.FStar_Tactics_Types.context
                 in
              match uu____4953 with
              | FStar_Pervasives_Native.None  ->
                  fail "Cannot clear; binder not in environment"
              | FStar_Pervasives_Native.Some (e',bvs) ->
                  let rec check bvs1 =
                    match bvs1 with
                    | [] -> ret ()
                    | bv'::bvs2 ->
                        let uu____4998 =
                          free_in bv bv'.FStar_Syntax_Syntax.sort  in
                        if uu____4998
                        then
                          let uu____5001 =
                            let uu____5002 =
                              FStar_Syntax_Print.bv_to_string bv'  in
                            FStar_Util.format1
                              "Cannot clear; binder present in the type of %s"
                              uu____5002
                             in
                          fail uu____5001
                        else check bvs2
                     in
                  let uu____5004 =
                    free_in bv goal.FStar_Tactics_Types.goal_ty  in
                  if uu____5004
                  then fail "Cannot clear; binder present in goal"
                  else
                    (let uu____5008 = check bvs  in
                     bind uu____5008
                       (fun uu____5014  ->
                          let env' = push_bvs e' bvs  in
                          let uu____5016 =
                            new_uvar "clear.witness" env'
                              goal.FStar_Tactics_Types.goal_ty
                             in
                          bind uu____5016
                            (fun ut  ->
                               let uu____5022 =
                                 do_unify goal.FStar_Tactics_Types.context
                                   goal.FStar_Tactics_Types.witness ut
                                  in
                               if uu____5022
                               then
                                 replace_cur
                                   (let uu___98_5027 = goal  in
                                    {
                                      FStar_Tactics_Types.context = env';
                                      FStar_Tactics_Types.witness = ut;
                                      FStar_Tactics_Types.goal_ty =
                                        (uu___98_5027.FStar_Tactics_Types.goal_ty);
                                      FStar_Tactics_Types.opts =
                                        (uu___98_5027.FStar_Tactics_Types.opts);
                                      FStar_Tactics_Types.is_guard =
                                        (uu___98_5027.FStar_Tactics_Types.is_guard)
                                    })
                               else
                                 fail
                                   "Cannot clear; binder appears in witness")))))
  
let (clear_top : Prims.unit tac) =
  bind cur_goal
    (fun goal  ->
       let uu____5036 =
         FStar_TypeChecker_Env.pop_bv goal.FStar_Tactics_Types.context  in
       match uu____5036 with
       | FStar_Pervasives_Native.None  -> fail "Cannot clear; empty context"
       | FStar_Pervasives_Native.Some (x,uu____5050) ->
           let uu____5055 = FStar_Syntax_Syntax.mk_binder x  in
           clear uu____5055)
  
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
           let uu___99_5071 = g  in
           {
             FStar_Tactics_Types.context = ctx';
             FStar_Tactics_Types.witness =
               (uu___99_5071.FStar_Tactics_Types.witness);
             FStar_Tactics_Types.goal_ty =
               (uu___99_5071.FStar_Tactics_Types.goal_ty);
             FStar_Tactics_Types.opts =
               (uu___99_5071.FStar_Tactics_Types.opts);
             FStar_Tactics_Types.is_guard =
               (uu___99_5071.FStar_Tactics_Types.is_guard)
           }  in
         bind dismiss (fun uu____5073  -> add_goals [g']))
  
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
           let uu___100_5089 = g  in
           {
             FStar_Tactics_Types.context = ctx';
             FStar_Tactics_Types.witness =
               (uu___100_5089.FStar_Tactics_Types.witness);
             FStar_Tactics_Types.goal_ty =
               (uu___100_5089.FStar_Tactics_Types.goal_ty);
             FStar_Tactics_Types.opts =
               (uu___100_5089.FStar_Tactics_Types.opts);
             FStar_Tactics_Types.is_guard =
               (uu___100_5089.FStar_Tactics_Types.is_guard)
           }  in
         bind dismiss (fun uu____5091  -> add_goals [g']))
  
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
            let uu____5123 = FStar_Syntax_Subst.compress t  in
            uu____5123.FStar_Syntax_Syntax.n  in
          let uu____5126 =
            if d = FStar_Tactics_Types.TopDown
            then
              f env
                (let uu___102_5132 = t  in
                 {
                   FStar_Syntax_Syntax.n = tn;
                   FStar_Syntax_Syntax.pos =
                     (uu___102_5132.FStar_Syntax_Syntax.pos);
                   FStar_Syntax_Syntax.vars =
                     (uu___102_5132.FStar_Syntax_Syntax.vars)
                 })
            else ret t  in
          bind uu____5126
            (fun t1  ->
               let tn1 =
                 let uu____5140 =
                   let uu____5141 = FStar_Syntax_Subst.compress t1  in
                   uu____5141.FStar_Syntax_Syntax.n  in
                 match uu____5140 with
                 | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
                     let ff = tac_fold_env d f env  in
                     let uu____5173 = ff hd1  in
                     bind uu____5173
                       (fun hd2  ->
                          let fa uu____5193 =
                            match uu____5193 with
                            | (a,q) ->
                                let uu____5206 = ff a  in
                                bind uu____5206 (fun a1  -> ret (a1, q))
                             in
                          let uu____5219 = mapM fa args  in
                          bind uu____5219
                            (fun args1  ->
                               ret (FStar_Syntax_Syntax.Tm_app (hd2, args1))))
                 | FStar_Syntax_Syntax.Tm_abs (bs,t2,k) ->
                     let uu____5279 = FStar_Syntax_Subst.open_term bs t2  in
                     (match uu____5279 with
                      | (bs1,t') ->
                          let uu____5288 =
                            let uu____5291 =
                              FStar_TypeChecker_Env.push_binders env bs1  in
                            tac_fold_env d f uu____5291 t'  in
                          bind uu____5288
                            (fun t''  ->
                               let uu____5295 =
                                 let uu____5296 =
                                   let uu____5313 =
                                     FStar_Syntax_Subst.close_binders bs1  in
                                   let uu____5314 =
                                     FStar_Syntax_Subst.close bs1 t''  in
                                   (uu____5313, uu____5314, k)  in
                                 FStar_Syntax_Syntax.Tm_abs uu____5296  in
                               ret uu____5295))
                 | FStar_Syntax_Syntax.Tm_arrow (bs,k) -> ret tn
                 | uu____5335 -> ret tn  in
               bind tn1
                 (fun tn2  ->
                    let t' =
                      let uu___101_5342 = t1  in
                      {
                        FStar_Syntax_Syntax.n = tn2;
                        FStar_Syntax_Syntax.pos =
                          (uu___101_5342.FStar_Syntax_Syntax.pos);
                        FStar_Syntax_Syntax.vars =
                          (uu___101_5342.FStar_Syntax_Syntax.vars)
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
            let uu____5371 = FStar_TypeChecker_TcTerm.tc_term env t  in
            match uu____5371 with
            | (t1,lcomp,g) ->
                let uu____5383 =
                  (let uu____5386 =
                     FStar_Syntax_Util.is_pure_or_ghost_lcomp lcomp  in
                   Prims.op_Negation uu____5386) ||
                    (let uu____5388 = FStar_TypeChecker_Rel.is_trivial g  in
                     Prims.op_Negation uu____5388)
                   in
                if uu____5383
                then ret t1
                else
                  (let rewrite_eq =
                     let typ = lcomp.FStar_Syntax_Syntax.res_typ  in
                     let uu____5398 = new_uvar "pointwise_rec" env typ  in
                     bind uu____5398
                       (fun ut  ->
                          log ps
                            (fun uu____5409  ->
                               let uu____5410 =
                                 FStar_Syntax_Print.term_to_string t1  in
                               let uu____5411 =
                                 FStar_Syntax_Print.term_to_string ut  in
                               FStar_Util.print2
                                 "Pointwise_rec: making equality\n\t%s ==\n\t%s\n"
                                 uu____5410 uu____5411);
                          (let uu____5412 =
                             let uu____5415 =
                               let uu____5416 =
                                 FStar_TypeChecker_TcTerm.universe_of env typ
                                  in
                               FStar_Syntax_Util.mk_eq2 uu____5416 typ t1 ut
                                in
                             add_irrelevant_goal "pointwise_rec equation" env
                               uu____5415 opts
                              in
                           bind uu____5412
                             (fun uu____5419  ->
                                let uu____5420 =
                                  bind tau
                                    (fun uu____5426  ->
                                       let ut1 =
                                         FStar_TypeChecker_Normalize.reduce_uvar_solutions
                                           env ut
                                          in
                                       log ps
                                         (fun uu____5432  ->
                                            let uu____5433 =
                                              FStar_Syntax_Print.term_to_string
                                                t1
                                               in
                                            let uu____5434 =
                                              FStar_Syntax_Print.term_to_string
                                                ut1
                                               in
                                            FStar_Util.print2
                                              "Pointwise_rec: succeeded rewriting\n\t%s to\n\t%s\n"
                                              uu____5433 uu____5434);
                                       ret ut1)
                                   in
                                focus uu____5420)))
                      in
                   let uu____5435 = trytac' rewrite_eq  in
                   bind uu____5435
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
           let uu____5477 =
             match ps.FStar_Tactics_Types.goals with
             | g::gs -> (g, gs)
             | [] -> failwith "Pointwise: no goals"  in
           match uu____5477 with
           | (g,gs) ->
               let gt1 = g.FStar_Tactics_Types.goal_ty  in
               (log ps
                  (fun uu____5514  ->
                     let uu____5515 = FStar_Syntax_Print.term_to_string gt1
                        in
                     FStar_Util.print1 "Pointwise starting with %s\n"
                       uu____5515);
                bind dismiss_all
                  (fun uu____5518  ->
                     let uu____5519 =
                       tac_fold_env d
                         (pointwise_rec ps tau g.FStar_Tactics_Types.opts)
                         g.FStar_Tactics_Types.context gt1
                        in
                     bind uu____5519
                       (fun gt'  ->
                          log ps
                            (fun uu____5529  ->
                               let uu____5530 =
                                 FStar_Syntax_Print.term_to_string gt'  in
                               FStar_Util.print1
                                 "Pointwise seems to have succeded with %s\n"
                                 uu____5530);
                          (let uu____5531 = push_goals gs  in
                           bind uu____5531
                             (fun uu____5535  ->
                                add_goals
                                  [(let uu___103_5537 = g  in
                                    {
                                      FStar_Tactics_Types.context =
                                        (uu___103_5537.FStar_Tactics_Types.context);
                                      FStar_Tactics_Types.witness =
                                        (uu___103_5537.FStar_Tactics_Types.witness);
                                      FStar_Tactics_Types.goal_ty = gt';
                                      FStar_Tactics_Types.opts =
                                        (uu___103_5537.FStar_Tactics_Types.opts);
                                      FStar_Tactics_Types.is_guard =
                                        (uu___103_5537.FStar_Tactics_Types.is_guard)
                                    })]))))))
  
let (trefl : Prims.unit tac) =
  bind cur_goal
    (fun g  ->
       let uu____5559 =
         FStar_Syntax_Util.un_squash g.FStar_Tactics_Types.goal_ty  in
       match uu____5559 with
       | FStar_Pervasives_Native.Some t ->
           let uu____5571 = FStar_Syntax_Util.head_and_args' t  in
           (match uu____5571 with
            | (hd1,args) ->
                let uu____5604 =
                  let uu____5617 =
                    let uu____5618 = FStar_Syntax_Util.un_uinst hd1  in
                    uu____5618.FStar_Syntax_Syntax.n  in
                  (uu____5617, args)  in
                (match uu____5604 with
                 | (FStar_Syntax_Syntax.Tm_fvar
                    fv,uu____5632::(l,uu____5634)::(r,uu____5636)::[]) when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.eq2_lid
                     ->
                     let uu____5683 =
                       let uu____5684 =
                         do_unify g.FStar_Tactics_Types.context l r  in
                       Prims.op_Negation uu____5684  in
                     if uu____5683
                     then
                       let uu____5687 = tts g.FStar_Tactics_Types.context l
                          in
                       let uu____5688 = tts g.FStar_Tactics_Types.context r
                          in
                       fail2 "trefl: not a trivial equality (%s vs %s)"
                         uu____5687 uu____5688
                     else solve g FStar_Syntax_Util.exp_unit
                 | (hd2,uu____5691) ->
                     let uu____5708 = tts g.FStar_Tactics_Types.context t  in
                     fail1 "trefl: not an equality (%s)" uu____5708))
       | FStar_Pervasives_Native.None  -> fail "not an irrelevant goal")
  
let (dup : Prims.unit tac) =
  bind cur_goal
    (fun g  ->
       let uu____5718 =
         new_uvar "dup" g.FStar_Tactics_Types.context
           g.FStar_Tactics_Types.goal_ty
          in
       bind uu____5718
         (fun u  ->
            let g' =
              let uu___104_5725 = g  in
              {
                FStar_Tactics_Types.context =
                  (uu___104_5725.FStar_Tactics_Types.context);
                FStar_Tactics_Types.witness = u;
                FStar_Tactics_Types.goal_ty =
                  (uu___104_5725.FStar_Tactics_Types.goal_ty);
                FStar_Tactics_Types.opts =
                  (uu___104_5725.FStar_Tactics_Types.opts);
                FStar_Tactics_Types.is_guard =
                  (uu___104_5725.FStar_Tactics_Types.is_guard)
              }  in
            bind dismiss
              (fun uu____5728  ->
                 let uu____5729 =
                   let uu____5732 =
                     let uu____5733 =
                       FStar_TypeChecker_TcTerm.universe_of
                         g.FStar_Tactics_Types.context
                         g.FStar_Tactics_Types.goal_ty
                        in
                     FStar_Syntax_Util.mk_eq2 uu____5733
                       g.FStar_Tactics_Types.goal_ty u
                       g.FStar_Tactics_Types.witness
                      in
                   add_irrelevant_goal "dup equation"
                     g.FStar_Tactics_Types.context uu____5732
                     g.FStar_Tactics_Types.opts
                    in
                 bind uu____5729
                   (fun uu____5736  ->
                      let uu____5737 = add_goals [g']  in
                      bind uu____5737 (fun uu____5741  -> ret ())))))
  
let (flip : Prims.unit tac) =
  bind get
    (fun ps  ->
       match ps.FStar_Tactics_Types.goals with
       | g1::g2::gs ->
           set
             (let uu___105_5760 = ps  in
              {
                FStar_Tactics_Types.main_context =
                  (uu___105_5760.FStar_Tactics_Types.main_context);
                FStar_Tactics_Types.main_goal =
                  (uu___105_5760.FStar_Tactics_Types.main_goal);
                FStar_Tactics_Types.all_implicits =
                  (uu___105_5760.FStar_Tactics_Types.all_implicits);
                FStar_Tactics_Types.goals = (g2 :: g1 :: gs);
                FStar_Tactics_Types.smt_goals =
                  (uu___105_5760.FStar_Tactics_Types.smt_goals);
                FStar_Tactics_Types.depth =
                  (uu___105_5760.FStar_Tactics_Types.depth);
                FStar_Tactics_Types.__dump =
                  (uu___105_5760.FStar_Tactics_Types.__dump);
                FStar_Tactics_Types.psc =
                  (uu___105_5760.FStar_Tactics_Types.psc);
                FStar_Tactics_Types.entry_range =
                  (uu___105_5760.FStar_Tactics_Types.entry_range)
              })
       | uu____5761 -> fail "flip: less than 2 goals")
  
let (later : Prims.unit tac) =
  bind get
    (fun ps  ->
       match ps.FStar_Tactics_Types.goals with
       | [] -> ret ()
       | g::gs ->
           set
             (let uu___106_5778 = ps  in
              {
                FStar_Tactics_Types.main_context =
                  (uu___106_5778.FStar_Tactics_Types.main_context);
                FStar_Tactics_Types.main_goal =
                  (uu___106_5778.FStar_Tactics_Types.main_goal);
                FStar_Tactics_Types.all_implicits =
                  (uu___106_5778.FStar_Tactics_Types.all_implicits);
                FStar_Tactics_Types.goals = (FStar_List.append gs [g]);
                FStar_Tactics_Types.smt_goals =
                  (uu___106_5778.FStar_Tactics_Types.smt_goals);
                FStar_Tactics_Types.depth =
                  (uu___106_5778.FStar_Tactics_Types.depth);
                FStar_Tactics_Types.__dump =
                  (uu___106_5778.FStar_Tactics_Types.__dump);
                FStar_Tactics_Types.psc =
                  (uu___106_5778.FStar_Tactics_Types.psc);
                FStar_Tactics_Types.entry_range =
                  (uu___106_5778.FStar_Tactics_Types.entry_range)
              }))
  
let (qed : Prims.unit tac) =
  bind get
    (fun ps  ->
       match ps.FStar_Tactics_Types.goals with
       | [] -> ret ()
       | uu____5787 -> fail "Not done!")
  
let (cases :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 tac)
  =
  fun t  ->
    let uu____5805 =
      bind cur_goal
        (fun g  ->
           let uu____5819 = __tc g.FStar_Tactics_Types.context t  in
           bind uu____5819
             (fun uu____5855  ->
                match uu____5855 with
                | (t1,typ,guard) ->
                    let uu____5871 = FStar_Syntax_Util.head_and_args typ  in
                    (match uu____5871 with
                     | (hd1,args) ->
                         let uu____5914 =
                           let uu____5927 =
                             let uu____5928 = FStar_Syntax_Util.un_uinst hd1
                                in
                             uu____5928.FStar_Syntax_Syntax.n  in
                           (uu____5927, args)  in
                         (match uu____5914 with
                          | (FStar_Syntax_Syntax.Tm_fvar
                             fv,(p,uu____5947)::(q,uu____5949)::[]) when
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
                                let uu___107_5987 = g  in
                                let uu____5988 =
                                  FStar_TypeChecker_Env.push_bv
                                    g.FStar_Tactics_Types.context v_p
                                   in
                                {
                                  FStar_Tactics_Types.context = uu____5988;
                                  FStar_Tactics_Types.witness =
                                    (uu___107_5987.FStar_Tactics_Types.witness);
                                  FStar_Tactics_Types.goal_ty =
                                    (uu___107_5987.FStar_Tactics_Types.goal_ty);
                                  FStar_Tactics_Types.opts =
                                    (uu___107_5987.FStar_Tactics_Types.opts);
                                  FStar_Tactics_Types.is_guard =
                                    (uu___107_5987.FStar_Tactics_Types.is_guard)
                                }  in
                              let g2 =
                                let uu___108_5990 = g  in
                                let uu____5991 =
                                  FStar_TypeChecker_Env.push_bv
                                    g.FStar_Tactics_Types.context v_q
                                   in
                                {
                                  FStar_Tactics_Types.context = uu____5991;
                                  FStar_Tactics_Types.witness =
                                    (uu___108_5990.FStar_Tactics_Types.witness);
                                  FStar_Tactics_Types.goal_ty =
                                    (uu___108_5990.FStar_Tactics_Types.goal_ty);
                                  FStar_Tactics_Types.opts =
                                    (uu___108_5990.FStar_Tactics_Types.opts);
                                  FStar_Tactics_Types.is_guard =
                                    (uu___108_5990.FStar_Tactics_Types.is_guard)
                                }  in
                              bind dismiss
                                (fun uu____5998  ->
                                   let uu____5999 = add_goals [g1; g2]  in
                                   bind uu____5999
                                     (fun uu____6008  ->
                                        let uu____6009 =
                                          let uu____6014 =
                                            FStar_Syntax_Syntax.bv_to_name
                                              v_p
                                             in
                                          let uu____6015 =
                                            FStar_Syntax_Syntax.bv_to_name
                                              v_q
                                             in
                                          (uu____6014, uu____6015)  in
                                        ret uu____6009))
                          | uu____6020 ->
                              let uu____6033 =
                                tts g.FStar_Tactics_Types.context typ  in
                              fail1 "Not a disjunction: %s" uu____6033))))
       in
    FStar_All.pipe_left (wrap_err "cases") uu____5805
  
let (set_options : Prims.string -> Prims.unit tac) =
  fun s  ->
    bind cur_goal
      (fun g  ->
         FStar_Options.push ();
         (let uu____6071 = FStar_Util.smap_copy g.FStar_Tactics_Types.opts
             in
          FStar_Options.set uu____6071);
         (let res = FStar_Options.set_options FStar_Options.Set s  in
          let opts' = FStar_Options.peek ()  in
          FStar_Options.pop ();
          (match res with
           | FStar_Getopt.Success  ->
               let g' =
                 let uu___109_6078 = g  in
                 {
                   FStar_Tactics_Types.context =
                     (uu___109_6078.FStar_Tactics_Types.context);
                   FStar_Tactics_Types.witness =
                     (uu___109_6078.FStar_Tactics_Types.witness);
                   FStar_Tactics_Types.goal_ty =
                     (uu___109_6078.FStar_Tactics_Types.goal_ty);
                   FStar_Tactics_Types.opts = opts';
                   FStar_Tactics_Types.is_guard =
                     (uu___109_6078.FStar_Tactics_Types.is_guard)
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
      let uu____6122 =
        bind cur_goal
          (fun goal  ->
             let env =
               FStar_TypeChecker_Env.set_expected_typ
                 goal.FStar_Tactics_Types.context ty
                in
             let uu____6130 = __tc env tm  in
             bind uu____6130
               (fun uu____6150  ->
                  match uu____6150 with
                  | (tm1,typ,guard) ->
                      (FStar_TypeChecker_Rel.force_trivial_guard env guard;
                       ret tm1)))
         in
      FStar_All.pipe_left (wrap_err "unquote") uu____6122
  
let (uvar_env :
  env ->
    FStar_Syntax_Syntax.typ FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.term tac)
  =
  fun env  ->
    fun ty  ->
      let uu____6181 =
        match ty with
        | FStar_Pervasives_Native.Some ty1 -> ret ty1
        | FStar_Pervasives_Native.None  ->
            let uu____6187 =
              let uu____6188 = FStar_Syntax_Util.type_u ()  in
              FStar_All.pipe_left FStar_Pervasives_Native.fst uu____6188  in
            new_uvar "uvar_env.2" env uu____6187
         in
      bind uu____6181
        (fun typ  ->
           let uu____6200 = new_uvar "uvar_env" env typ  in
           bind uu____6200 (fun t  -> ret t))
  
let (unshelve : FStar_Syntax_Syntax.term -> Prims.unit tac) =
  fun t  ->
    let uu____6212 =
      bind cur_goal
        (fun goal  ->
           let uu____6218 = __tc goal.FStar_Tactics_Types.context t  in
           bind uu____6218
             (fun uu____6238  ->
                match uu____6238 with
                | (t1,typ,guard) ->
                    let uu____6250 =
                      must_trivial goal.FStar_Tactics_Types.context guard  in
                    bind uu____6250
                      (fun uu____6255  ->
                         let uu____6256 =
                           let uu____6259 =
                             let uu___110_6260 = goal  in
                             let uu____6261 =
                               bnorm goal.FStar_Tactics_Types.context t1  in
                             let uu____6262 =
                               bnorm goal.FStar_Tactics_Types.context typ  in
                             {
                               FStar_Tactics_Types.context =
                                 (uu___110_6260.FStar_Tactics_Types.context);
                               FStar_Tactics_Types.witness = uu____6261;
                               FStar_Tactics_Types.goal_ty = uu____6262;
                               FStar_Tactics_Types.opts =
                                 (uu___110_6260.FStar_Tactics_Types.opts);
                               FStar_Tactics_Types.is_guard = false
                             }  in
                           [uu____6259]  in
                         add_goals uu____6256)))
       in
    FStar_All.pipe_left (wrap_err "unshelve") uu____6212
  
let (unify :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool tac) =
  fun t1  ->
    fun t2  ->
      bind get
        (fun ps  ->
           let uu____6280 =
             do_unify ps.FStar_Tactics_Types.main_context t1 t2  in
           ret uu____6280)
  
let (launch_process :
  Prims.string -> Prims.string -> Prims.string -> Prims.string tac) =
  fun prog  ->
    fun args  ->
      fun input  ->
        bind idtac
          (fun uu____6297  ->
             let uu____6298 = FStar_Options.unsafe_tactic_exec ()  in
             if uu____6298
             then
               let s =
                 FStar_Util.launch_process true "tactic_launch" prog args
                   input (fun uu____6304  -> fun uu____6305  -> false)
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
        (fun uu____6319  ->
           let uu____6320 =
             FStar_Syntax_Syntax.gen_bv nm FStar_Pervasives_Native.None t  in
           ret uu____6320)
  
let (goal_of_goal_ty :
  env ->
    FStar_Syntax_Syntax.typ ->
      (FStar_Tactics_Types.goal,FStar_TypeChecker_Env.guard_t)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun typ  ->
      let uu____6335 =
        FStar_TypeChecker_Util.new_implicit_var "proofstate_of_goal_ty"
          typ.FStar_Syntax_Syntax.pos env typ
         in
      match uu____6335 with
      | (u,uu____6353,g_u) ->
          let g =
            let uu____6368 = FStar_Options.peek ()  in
            {
              FStar_Tactics_Types.context = env;
              FStar_Tactics_Types.witness = u;
              FStar_Tactics_Types.goal_ty = typ;
              FStar_Tactics_Types.opts = uu____6368;
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
      let uu____6379 = goal_of_goal_ty env typ  in
      match uu____6379 with
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
  