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
  
let (remove_implicits : implicits -> Prims.unit tac) =
  fun js  ->
    let exists_in_j uu____1226 =
      match uu____1226 with
      | (uu____1239,uu____1240,u_i,uu____1242,uu____1243,uu____1244) ->
          FStar_All.pipe_right js
            (FStar_Util.for_some
               (fun uu____1264  ->
                  match uu____1264 with
                  | (uu____1277,uu____1278,u_j,uu____1280,uu____1281,uu____1282)
                      -> FStar_Syntax_Unionfind.equiv u_j u_i))
       in
    bind get
      (fun p  ->
         let uu____1286 =
           let uu___68_1287 = p  in
           let uu____1288 =
             FStar_All.pipe_right p.FStar_Tactics_Types.all_implicits
               (FStar_List.filter
                  (fun i  ->
                     let uu____1330 = exists_in_j i  in
                     Prims.op_Negation uu____1330))
              in
           {
             FStar_Tactics_Types.main_context =
               (uu___68_1287.FStar_Tactics_Types.main_context);
             FStar_Tactics_Types.main_goal =
               (uu___68_1287.FStar_Tactics_Types.main_goal);
             FStar_Tactics_Types.all_implicits = uu____1288;
             FStar_Tactics_Types.goals =
               (uu___68_1287.FStar_Tactics_Types.goals);
             FStar_Tactics_Types.smt_goals =
               (uu___68_1287.FStar_Tactics_Types.smt_goals);
             FStar_Tactics_Types.depth =
               (uu___68_1287.FStar_Tactics_Types.depth);
             FStar_Tactics_Types.__dump =
               (uu___68_1287.FStar_Tactics_Types.__dump);
             FStar_Tactics_Types.psc = (uu___68_1287.FStar_Tactics_Types.psc);
             FStar_Tactics_Types.entry_range =
               (uu___68_1287.FStar_Tactics_Types.entry_range)
           }  in
         set uu____1286)
  
let (new_uvar_i :
  Prims.string ->
    env ->
      FStar_Syntax_Syntax.typ ->
        (FStar_Syntax_Syntax.term,implicits) FStar_Pervasives_Native.tuple2
          tac)
  =
  fun reason  ->
    fun env  ->
      fun typ  ->
        let uu____1352 =
          FStar_TypeChecker_Util.new_implicit_var reason
            typ.FStar_Syntax_Syntax.pos env typ
           in
        match uu____1352 with
        | (u,uu____1372,g_u) ->
            let uu____1386 =
              add_implicits g_u.FStar_TypeChecker_Env.implicits  in
            bind uu____1386
              (fun uu____1408  ->
                 ret (u, (g_u.FStar_TypeChecker_Env.implicits)))
  
let (new_uvar :
  Prims.string ->
    env -> FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.term tac)
  =
  fun reason  ->
    fun env  ->
      fun typ  ->
        let uu____1454 =
          FStar_TypeChecker_Util.new_implicit_var reason
            typ.FStar_Syntax_Syntax.pos env typ
           in
        match uu____1454 with
        | (u,uu____1470,g_u) ->
            let uu____1484 =
              add_implicits g_u.FStar_TypeChecker_Env.implicits  in
            bind uu____1484 (fun uu____1488  -> ret u)
  
let (is_true : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____1492 = FStar_Syntax_Util.un_squash t  in
    match uu____1492 with
    | FStar_Pervasives_Native.Some t' ->
        let uu____1502 =
          let uu____1503 = FStar_Syntax_Subst.compress t'  in
          uu____1503.FStar_Syntax_Syntax.n  in
        (match uu____1502 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.true_lid
         | uu____1507 -> false)
    | uu____1508 -> false
  
let (is_false : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____1516 = FStar_Syntax_Util.un_squash t  in
    match uu____1516 with
    | FStar_Pervasives_Native.Some t' ->
        let uu____1526 =
          let uu____1527 = FStar_Syntax_Subst.compress t'  in
          uu____1527.FStar_Syntax_Syntax.n  in
        (match uu____1526 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.false_lid
         | uu____1531 -> false)
    | uu____1532 -> false
  
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
            let uu____1572 = env.FStar_TypeChecker_Env.universe_of env phi
               in
            FStar_Syntax_Util.mk_squash uu____1572 phi  in
          let uu____1573 = new_uvar reason env typ  in
          bind uu____1573
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
             let uu____1629 =
               (ps.FStar_Tactics_Types.main_context).FStar_TypeChecker_Env.type_of
                 e t
                in
             ret uu____1629
           with
           | ex ->
               let uu____1656 = tts e t  in
               let uu____1657 =
                 let uu____1658 = FStar_TypeChecker_Env.all_binders e  in
                 FStar_All.pipe_right uu____1658
                   (FStar_Syntax_Print.binders_to_string ", ")
                  in
               fail2 "Cannot type %s in context (%s)" uu____1656 uu____1657)
  
let (must_trivial : env -> FStar_TypeChecker_Env.guard_t -> Prims.unit tac) =
  fun e  ->
    fun g  ->
      try
        let uu____1682 =
          let uu____1683 =
            let uu____1684 = FStar_TypeChecker_Rel.discharge_guard_no_smt e g
               in
            FStar_All.pipe_left FStar_TypeChecker_Rel.is_trivial uu____1684
             in
          Prims.op_Negation uu____1683  in
        if uu____1682 then fail "got non-trivial guard" else ret ()
      with | uu____1693 -> fail "got non-trivial guard"
  
let (tc : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.typ tac) =
  fun t  ->
    let uu____1701 =
      bind cur_goal
        (fun goal  ->
           let uu____1707 = __tc goal.FStar_Tactics_Types.context t  in
           bind uu____1707
             (fun uu____1727  ->
                match uu____1727 with
                | (t1,typ,guard) ->
                    let uu____1739 =
                      must_trivial goal.FStar_Tactics_Types.context guard  in
                    bind uu____1739 (fun uu____1743  -> ret typ)))
       in
    FStar_All.pipe_left (wrap_err "tc") uu____1701
  
let (add_irrelevant_goal :
  Prims.string ->
    env ->
      FStar_Syntax_Syntax.typ -> FStar_Options.optionstate -> Prims.unit tac)
  =
  fun reason  ->
    fun env  ->
      fun phi  ->
        fun opts  ->
          let uu____1764 = mk_irrelevant_goal reason env phi opts  in
          bind uu____1764 (fun goal  -> add_goals [goal])
  
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
       let uu____1786 =
         istrivial goal.FStar_Tactics_Types.context
           goal.FStar_Tactics_Types.goal_ty
          in
       if uu____1786
       then solve goal FStar_Syntax_Util.exp_unit
       else
         (let uu____1790 =
            tts goal.FStar_Tactics_Types.context
              goal.FStar_Tactics_Types.goal_ty
             in
          fail1 "Not a trivial goal: %s" uu____1790))
  
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
          let uu____1807 =
            let uu____1808 = FStar_TypeChecker_Rel.simplify_guard e g  in
            uu____1808.FStar_TypeChecker_Env.guard_f  in
          match uu____1807 with
          | FStar_TypeChecker_Common.Trivial  -> ret ()
          | FStar_TypeChecker_Common.NonTrivial f ->
              let uu____1812 = istrivial e f  in
              if uu____1812
              then ret ()
              else
                (let uu____1816 = mk_irrelevant_goal reason e f opts  in
                 bind uu____1816
                   (fun goal  ->
                      let goal1 =
                        let uu___73_1823 = goal  in
                        {
                          FStar_Tactics_Types.context =
                            (uu___73_1823.FStar_Tactics_Types.context);
                          FStar_Tactics_Types.witness =
                            (uu___73_1823.FStar_Tactics_Types.witness);
                          FStar_Tactics_Types.goal_ty =
                            (uu___73_1823.FStar_Tactics_Types.goal_ty);
                          FStar_Tactics_Types.opts =
                            (uu___73_1823.FStar_Tactics_Types.opts);
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
          let uu____1844 =
            let uu____1845 = FStar_TypeChecker_Rel.simplify_guard e g  in
            uu____1845.FStar_TypeChecker_Env.guard_f  in
          match uu____1844 with
          | FStar_TypeChecker_Common.Trivial  ->
              ret FStar_Pervasives_Native.None
          | FStar_TypeChecker_Common.NonTrivial f ->
              let uu____1853 = istrivial e f  in
              if uu____1853
              then ret FStar_Pervasives_Native.None
              else
                (let uu____1861 = mk_irrelevant_goal reason e f opts  in
                 bind uu____1861
                   (fun goal  ->
                      ret
                        (FStar_Pervasives_Native.Some
                           (let uu___74_1871 = goal  in
                            {
                              FStar_Tactics_Types.context =
                                (uu___74_1871.FStar_Tactics_Types.context);
                              FStar_Tactics_Types.witness =
                                (uu___74_1871.FStar_Tactics_Types.witness);
                              FStar_Tactics_Types.goal_ty =
                                (uu___74_1871.FStar_Tactics_Types.goal_ty);
                              FStar_Tactics_Types.opts =
                                (uu___74_1871.FStar_Tactics_Types.opts);
                              FStar_Tactics_Types.is_guard = true
                            }))))
  
let (smt : Prims.unit tac) =
  bind cur_goal
    (fun g  ->
       let uu____1879 = is_irrelevant g  in
       if uu____1879
       then bind dismiss (fun uu____1883  -> add_smt_goals [g])
       else
         (let uu____1885 =
            tts g.FStar_Tactics_Types.context g.FStar_Tactics_Types.goal_ty
             in
          fail1 "goal is not irrelevant: cannot dispatch to smt (%s)"
            uu____1885))
  
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
             let uu____1926 =
               try
                 let uu____1960 =
                   let uu____1969 = FStar_BigInt.to_int_fs n1  in
                   FStar_List.splitAt uu____1969 p.FStar_Tactics_Types.goals
                    in
                 ret uu____1960
               with | uu____1991 -> fail "divide: not enough goals"  in
             bind uu____1926
               (fun uu____2018  ->
                  match uu____2018 with
                  | (lgs,rgs) ->
                      let lp =
                        let uu___75_2044 = p  in
                        {
                          FStar_Tactics_Types.main_context =
                            (uu___75_2044.FStar_Tactics_Types.main_context);
                          FStar_Tactics_Types.main_goal =
                            (uu___75_2044.FStar_Tactics_Types.main_goal);
                          FStar_Tactics_Types.all_implicits =
                            (uu___75_2044.FStar_Tactics_Types.all_implicits);
                          FStar_Tactics_Types.goals = lgs;
                          FStar_Tactics_Types.smt_goals = [];
                          FStar_Tactics_Types.depth =
                            (uu___75_2044.FStar_Tactics_Types.depth);
                          FStar_Tactics_Types.__dump =
                            (uu___75_2044.FStar_Tactics_Types.__dump);
                          FStar_Tactics_Types.psc =
                            (uu___75_2044.FStar_Tactics_Types.psc);
                          FStar_Tactics_Types.entry_range =
                            (uu___75_2044.FStar_Tactics_Types.entry_range)
                        }  in
                      let rp =
                        let uu___76_2046 = p  in
                        {
                          FStar_Tactics_Types.main_context =
                            (uu___76_2046.FStar_Tactics_Types.main_context);
                          FStar_Tactics_Types.main_goal =
                            (uu___76_2046.FStar_Tactics_Types.main_goal);
                          FStar_Tactics_Types.all_implicits =
                            (uu___76_2046.FStar_Tactics_Types.all_implicits);
                          FStar_Tactics_Types.goals = rgs;
                          FStar_Tactics_Types.smt_goals = [];
                          FStar_Tactics_Types.depth =
                            (uu___76_2046.FStar_Tactics_Types.depth);
                          FStar_Tactics_Types.__dump =
                            (uu___76_2046.FStar_Tactics_Types.__dump);
                          FStar_Tactics_Types.psc =
                            (uu___76_2046.FStar_Tactics_Types.psc);
                          FStar_Tactics_Types.entry_range =
                            (uu___76_2046.FStar_Tactics_Types.entry_range)
                        }  in
                      let uu____2047 = set lp  in
                      bind uu____2047
                        (fun uu____2055  ->
                           bind l
                             (fun a  ->
                                bind get
                                  (fun lp'  ->
                                     let uu____2069 = set rp  in
                                     bind uu____2069
                                       (fun uu____2077  ->
                                          bind r
                                            (fun b  ->
                                               bind get
                                                 (fun rp'  ->
                                                    let p' =
                                                      let uu___77_2093 = p
                                                         in
                                                      {
                                                        FStar_Tactics_Types.main_context
                                                          =
                                                          (uu___77_2093.FStar_Tactics_Types.main_context);
                                                        FStar_Tactics_Types.main_goal
                                                          =
                                                          (uu___77_2093.FStar_Tactics_Types.main_goal);
                                                        FStar_Tactics_Types.all_implicits
                                                          =
                                                          (uu___77_2093.FStar_Tactics_Types.all_implicits);
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
                                                          (uu___77_2093.FStar_Tactics_Types.depth);
                                                        FStar_Tactics_Types.__dump
                                                          =
                                                          (uu___77_2093.FStar_Tactics_Types.__dump);
                                                        FStar_Tactics_Types.psc
                                                          =
                                                          (uu___77_2093.FStar_Tactics_Types.psc);
                                                        FStar_Tactics_Types.entry_range
                                                          =
                                                          (uu___77_2093.FStar_Tactics_Types.entry_range)
                                                      }  in
                                                    let uu____2094 = set p'
                                                       in
                                                    bind uu____2094
                                                      (fun uu____2102  ->
                                                         ret (a, b))))))))))
  
let focus : 'a . 'a tac -> 'a tac =
  fun f  ->
    let uu____2120 = divide FStar_BigInt.one f idtac  in
    bind uu____2120
      (fun uu____2133  -> match uu____2133 with | (a,()) -> ret a)
  
let rec map : 'a . 'a tac -> 'a Prims.list tac =
  fun tau  ->
    bind get
      (fun p  ->
         match p.FStar_Tactics_Types.goals with
         | [] -> ret []
         | uu____2167::uu____2168 ->
             let uu____2171 =
               let uu____2180 = map tau  in
               divide FStar_BigInt.one tau uu____2180  in
             bind uu____2171
               (fun uu____2198  ->
                  match uu____2198 with | (h,t) -> ret (h :: t)))
  
let (seq : Prims.unit tac -> Prims.unit tac -> Prims.unit tac) =
  fun t1  ->
    fun t2  ->
      let uu____2235 =
        bind t1
          (fun uu____2240  ->
             let uu____2241 = map t2  in
             bind uu____2241 (fun uu____2249  -> ret ()))
         in
      focus uu____2235
  
let (intro : FStar_Syntax_Syntax.binder tac) =
  let uu____2256 =
    bind cur_goal
      (fun goal  ->
         let uu____2265 =
           FStar_Syntax_Util.arrow_one goal.FStar_Tactics_Types.goal_ty  in
         match uu____2265 with
         | FStar_Pervasives_Native.Some (b,c) ->
             let uu____2280 =
               let uu____2281 = FStar_Syntax_Util.is_total_comp c  in
               Prims.op_Negation uu____2281  in
             if uu____2280
             then fail "Codomain is effectful"
             else
               (let env' =
                  FStar_TypeChecker_Env.push_binders
                    goal.FStar_Tactics_Types.context [b]
                   in
                let typ' = comp_to_typ c  in
                let uu____2287 = new_uvar "intro" env' typ'  in
                bind uu____2287
                  (fun u  ->
                     let uu____2294 =
                       let uu____2295 =
                         FStar_Syntax_Util.abs [b] u
                           FStar_Pervasives_Native.None
                          in
                       trysolve goal uu____2295  in
                     if uu____2294
                     then
                       let uu____2298 =
                         let uu____2301 =
                           let uu___80_2302 = goal  in
                           let uu____2303 = bnorm env' u  in
                           let uu____2304 = bnorm env' typ'  in
                           {
                             FStar_Tactics_Types.context = env';
                             FStar_Tactics_Types.witness = uu____2303;
                             FStar_Tactics_Types.goal_ty = uu____2304;
                             FStar_Tactics_Types.opts =
                               (uu___80_2302.FStar_Tactics_Types.opts);
                             FStar_Tactics_Types.is_guard =
                               (uu___80_2302.FStar_Tactics_Types.is_guard)
                           }  in
                         replace_cur uu____2301  in
                       bind uu____2298 (fun uu____2306  -> ret b)
                     else fail "unification failed"))
         | FStar_Pervasives_Native.None  ->
             let uu____2312 =
               tts goal.FStar_Tactics_Types.context
                 goal.FStar_Tactics_Types.goal_ty
                in
             fail1 "goal is not an arrow (%s)" uu____2312)
     in
  FStar_All.pipe_left (wrap_err "intro") uu____2256 
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
       (let uu____2343 =
          FStar_Syntax_Util.arrow_one goal.FStar_Tactics_Types.goal_ty  in
        match uu____2343 with
        | FStar_Pervasives_Native.Some (b,c) ->
            let uu____2362 =
              let uu____2363 = FStar_Syntax_Util.is_total_comp c  in
              Prims.op_Negation uu____2363  in
            if uu____2362
            then fail "Codomain is effectful"
            else
              (let bv =
                 FStar_Syntax_Syntax.gen_bv "__recf"
                   FStar_Pervasives_Native.None
                   goal.FStar_Tactics_Types.goal_ty
                  in
               let bs =
                 let uu____2379 = FStar_Syntax_Syntax.mk_binder bv  in
                 [uu____2379; b]  in
               let env' =
                 FStar_TypeChecker_Env.push_binders
                   goal.FStar_Tactics_Types.context bs
                  in
               let uu____2381 =
                 let uu____2384 = comp_to_typ c  in
                 new_uvar "intro_rec" env' uu____2384  in
               bind uu____2381
                 (fun u  ->
                    let lb =
                      let uu____2400 =
                        FStar_Syntax_Util.abs [b] u
                          FStar_Pervasives_Native.None
                         in
                      FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl bv) []
                        goal.FStar_Tactics_Types.goal_ty
                        FStar_Parser_Const.effect_Tot_lid uu____2400 []
                        FStar_Range.dummyRange
                       in
                    let body = FStar_Syntax_Syntax.bv_to_name bv  in
                    let uu____2406 =
                      FStar_Syntax_Subst.close_let_rec [lb] body  in
                    match uu____2406 with
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
                          let uu____2443 =
                            let uu____2446 =
                              let uu___81_2447 = goal  in
                              let uu____2448 = bnorm env' u  in
                              let uu____2449 =
                                let uu____2450 = comp_to_typ c  in
                                bnorm env' uu____2450  in
                              {
                                FStar_Tactics_Types.context = env';
                                FStar_Tactics_Types.witness = uu____2448;
                                FStar_Tactics_Types.goal_ty = uu____2449;
                                FStar_Tactics_Types.opts =
                                  (uu___81_2447.FStar_Tactics_Types.opts);
                                FStar_Tactics_Types.is_guard =
                                  (uu___81_2447.FStar_Tactics_Types.is_guard)
                              }  in
                            replace_cur uu____2446  in
                          bind uu____2443
                            (fun uu____2457  ->
                               let uu____2458 =
                                 let uu____2463 =
                                   FStar_Syntax_Syntax.mk_binder bv  in
                                 (uu____2463, b)  in
                               ret uu____2458)
                        else fail "intro_rec: unification failed"))
        | FStar_Pervasives_Native.None  ->
            let uu____2477 =
              tts goal.FStar_Tactics_Types.context
                goal.FStar_Tactics_Types.goal_ty
               in
            fail1 "intro_rec: goal is not an arrow (%s)" uu____2477))
  
let (norm : FStar_Syntax_Embeddings.norm_step Prims.list -> Prims.unit tac) =
  fun s  ->
    bind cur_goal
      (fun goal  ->
         mlog
           (fun uu____2497  ->
              let uu____2498 =
                FStar_Syntax_Print.term_to_string
                  goal.FStar_Tactics_Types.witness
                 in
              FStar_Util.print1 "norm: witness = %s\n" uu____2498)
           (fun uu____2503  ->
              let steps =
                let uu____2507 = FStar_TypeChecker_Normalize.tr_norm_steps s
                   in
                FStar_List.append
                  [FStar_TypeChecker_Normalize.Reify;
                  FStar_TypeChecker_Normalize.UnfoldTac] uu____2507
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
                (let uu___82_2514 = goal  in
                 {
                   FStar_Tactics_Types.context =
                     (uu___82_2514.FStar_Tactics_Types.context);
                   FStar_Tactics_Types.witness = w;
                   FStar_Tactics_Types.goal_ty = t;
                   FStar_Tactics_Types.opts =
                     (uu___82_2514.FStar_Tactics_Types.opts);
                   FStar_Tactics_Types.is_guard =
                     (uu___82_2514.FStar_Tactics_Types.is_guard)
                 })))
  
let (norm_term_env :
  env ->
    FStar_Syntax_Embeddings.norm_step Prims.list ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac)
  =
  fun e  ->
    fun s  ->
      fun t  ->
        let uu____2532 =
          mlog
            (fun uu____2537  ->
               let uu____2538 = FStar_Syntax_Print.term_to_string t  in
               FStar_Util.print1 "norm_term: tm = %s\n" uu____2538)
            (fun uu____2540  ->
               bind get
                 (fun ps  ->
                    mlog
                      (fun uu____2545  ->
                         let uu____2546 =
                           tts ps.FStar_Tactics_Types.main_context t  in
                         FStar_Util.print1 "norm_term_env: t = %s\n"
                           uu____2546)
                      (fun uu____2549  ->
                         let uu____2550 = __tc e t  in
                         bind uu____2550
                           (fun uu____2572  ->
                              match uu____2572 with
                              | (t1,uu____2582,guard) ->
                                  (FStar_TypeChecker_Rel.force_trivial_guard
                                     e guard;
                                   (let steps =
                                      let uu____2588 =
                                        FStar_TypeChecker_Normalize.tr_norm_steps
                                          s
                                         in
                                      FStar_List.append
                                        [FStar_TypeChecker_Normalize.Reify;
                                        FStar_TypeChecker_Normalize.UnfoldTac]
                                        uu____2588
                                       in
                                    let t2 =
                                      normalize steps
                                        ps.FStar_Tactics_Types.main_context
                                        t1
                                       in
                                    ret t2))))))
           in
        FStar_All.pipe_left (wrap_err "norm_term") uu____2532
  
let (refine_intro : Prims.unit tac) =
  let uu____2600 =
    bind cur_goal
      (fun g  ->
         let uu____2607 =
           FStar_TypeChecker_Rel.base_and_refinement
             g.FStar_Tactics_Types.context g.FStar_Tactics_Types.goal_ty
            in
         match uu____2607 with
         | (uu____2620,FStar_Pervasives_Native.None ) ->
             fail "not a refinement"
         | (t,FStar_Pervasives_Native.Some (bv,phi)) ->
             let g1 =
               let uu___83_2645 = g  in
               {
                 FStar_Tactics_Types.context =
                   (uu___83_2645.FStar_Tactics_Types.context);
                 FStar_Tactics_Types.witness =
                   (uu___83_2645.FStar_Tactics_Types.witness);
                 FStar_Tactics_Types.goal_ty = t;
                 FStar_Tactics_Types.opts =
                   (uu___83_2645.FStar_Tactics_Types.opts);
                 FStar_Tactics_Types.is_guard =
                   (uu___83_2645.FStar_Tactics_Types.is_guard)
               }  in
             let uu____2646 =
               let uu____2651 =
                 let uu____2656 =
                   let uu____2657 = FStar_Syntax_Syntax.mk_binder bv  in
                   [uu____2657]  in
                 FStar_Syntax_Subst.open_term uu____2656 phi  in
               match uu____2651 with
               | (bvs,phi1) ->
                   let uu____2664 =
                     let uu____2665 = FStar_List.hd bvs  in
                     FStar_Pervasives_Native.fst uu____2665  in
                   (uu____2664, phi1)
                in
             (match uu____2646 with
              | (bv1,phi1) ->
                  let uu____2678 =
                    let uu____2681 =
                      FStar_Syntax_Subst.subst
                        [FStar_Syntax_Syntax.NT
                           (bv1, (g.FStar_Tactics_Types.witness))] phi1
                       in
                    mk_irrelevant_goal "refine_intro refinement"
                      g.FStar_Tactics_Types.context uu____2681
                      g.FStar_Tactics_Types.opts
                     in
                  bind uu____2678
                    (fun g2  ->
                       bind dismiss (fun uu____2685  -> add_goals [g1; g2]))))
     in
  FStar_All.pipe_left (wrap_err "refine_intro") uu____2600 
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
             let uu____2709 = __tc env t  in
             bind uu____2709
               (fun uu____2729  ->
                  match uu____2729 with
                  | (t1,typ,guard) ->
                      let uu____2741 =
                        if force_guard
                        then
                          must_trivial goal.FStar_Tactics_Types.context guard
                        else
                          add_goal_from_guard "__exact typing"
                            goal.FStar_Tactics_Types.context guard
                            goal.FStar_Tactics_Types.opts
                         in
                      bind uu____2741
                        (fun uu____2748  ->
                           mlog
                             (fun uu____2752  ->
                                let uu____2753 =
                                  tts goal.FStar_Tactics_Types.context typ
                                   in
                                let uu____2754 =
                                  tts goal.FStar_Tactics_Types.context
                                    goal.FStar_Tactics_Types.goal_ty
                                   in
                                FStar_Util.print2
                                  "exact: unifying %s and %s\n" uu____2753
                                  uu____2754)
                             (fun uu____2757  ->
                                let uu____2758 =
                                  do_unify goal.FStar_Tactics_Types.context
                                    typ goal.FStar_Tactics_Types.goal_ty
                                   in
                                if uu____2758
                                then solve goal t1
                                else
                                  (let uu____2762 =
                                     tts goal.FStar_Tactics_Types.context t1
                                      in
                                   let uu____2763 =
                                     tts goal.FStar_Tactics_Types.context typ
                                      in
                                   let uu____2764 =
                                     tts goal.FStar_Tactics_Types.context
                                       goal.FStar_Tactics_Types.goal_ty
                                      in
                                   let uu____2765 =
                                     tts goal.FStar_Tactics_Types.context
                                       goal.FStar_Tactics_Types.witness
                                      in
                                   fail4
                                     "%s : %s does not exactly solve the goal %s (witness = %s)"
                                     uu____2762 uu____2763 uu____2764
                                     uu____2765)))))
  
let (t_exact :
  Prims.bool -> Prims.bool -> FStar_Syntax_Syntax.term -> Prims.unit tac) =
  fun set_expected_typ1  ->
    fun force_guard  ->
      fun tm  ->
        let uu____2779 =
          mlog
            (fun uu____2784  ->
               let uu____2785 = FStar_Syntax_Print.term_to_string tm  in
               FStar_Util.print1 "t_exact: tm = %s\n" uu____2785)
            (fun uu____2788  ->
               let uu____2789 =
                 let uu____2796 =
                   __exact_now set_expected_typ1 force_guard tm  in
                 trytac' uu____2796  in
               bind uu____2789
                 (fun uu___56_2805  ->
                    match uu___56_2805 with
                    | FStar_Util.Inr r -> ret ()
                    | FStar_Util.Inl e ->
                        let uu____2814 =
                          let uu____2821 =
                            let uu____2824 =
                              norm [FStar_Syntax_Embeddings.Delta]  in
                            bind uu____2824
                              (fun uu____2828  ->
                                 bind refine_intro
                                   (fun uu____2830  ->
                                      __exact_now set_expected_typ1
                                        force_guard tm))
                             in
                          trytac' uu____2821  in
                        bind uu____2814
                          (fun uu___55_2837  ->
                             match uu___55_2837 with
                             | FStar_Util.Inr r -> ret ()
                             | FStar_Util.Inl uu____2845 -> fail e)))
           in
        FStar_All.pipe_left (wrap_err "exact") uu____2779
  
let (uvar_free_in_goal :
  FStar_Syntax_Syntax.uvar -> FStar_Tactics_Types.goal -> Prims.bool) =
  fun u  ->
    fun g  ->
      if g.FStar_Tactics_Types.is_guard
      then false
      else
        (let free_uvars =
           let uu____2860 =
             let uu____2867 =
               FStar_Syntax_Free.uvars g.FStar_Tactics_Types.goal_ty  in
             FStar_Util.set_elements uu____2867  in
           FStar_List.map FStar_Pervasives_Native.fst uu____2860  in
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
          let uu____2927 = f x  in
          bind uu____2927
            (fun y  ->
               let uu____2935 = mapM f xs  in
               bind uu____2935 (fun ys  -> ret (y :: ys)))
  
exception NoUnif 
let (uu___is_NoUnif : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with | NoUnif  -> true | uu____2953 -> false
  
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
               (fun uu____2971  ->
                  let uu____2972 = FStar_Syntax_Print.term_to_string tm  in
                  FStar_Util.print1 ">>> Calling __exact(%s)\n" uu____2972)
               (fun uu____2975  ->
                  let uu____2976 =
                    let uu____2981 = t_exact false true tm  in
                    trytac uu____2981  in
                  bind uu____2976
                    (fun uu___57_2988  ->
                       match uu___57_2988 with
                       | FStar_Pervasives_Native.Some r -> ret ()
                       | FStar_Pervasives_Native.None  ->
                           mlog
                             (fun uu____2996  ->
                                let uu____2997 =
                                  FStar_Syntax_Print.term_to_string typ  in
                                FStar_Util.print1 ">>> typ = %s\n" uu____2997)
                             (fun uu____3000  ->
                                let uu____3001 =
                                  FStar_Syntax_Util.arrow_one typ  in
                                match uu____3001 with
                                | FStar_Pervasives_Native.None  ->
                                    FStar_Exn.raise NoUnif
                                | FStar_Pervasives_Native.Some ((bv,aq),c) ->
                                    mlog
                                      (fun uu____3033  ->
                                         let uu____3034 =
                                           FStar_Syntax_Print.binder_to_string
                                             (bv, aq)
                                            in
                                         FStar_Util.print1
                                           "__apply: pushing binder %s\n"
                                           uu____3034)
                                      (fun uu____3037  ->
                                         let uu____3038 =
                                           let uu____3039 =
                                             FStar_Syntax_Util.is_total_comp
                                               c
                                              in
                                           Prims.op_Negation uu____3039  in
                                         if uu____3038
                                         then
                                           fail "apply: not total codomain"
                                         else
                                           (let uu____3043 =
                                              new_uvar "apply"
                                                goal.FStar_Tactics_Types.context
                                                bv.FStar_Syntax_Syntax.sort
                                               in
                                            bind uu____3043
                                              (fun u  ->
                                                 let tm' =
                                                   FStar_Syntax_Syntax.mk_Tm_app
                                                     tm [(u, aq)]
                                                     FStar_Pervasives_Native.None
                                                     tm.FStar_Syntax_Syntax.pos
                                                    in
                                                 let typ' =
                                                   let uu____3063 =
                                                     comp_to_typ c  in
                                                   FStar_All.pipe_left
                                                     (FStar_Syntax_Subst.subst
                                                        [FStar_Syntax_Syntax.NT
                                                           (bv, u)])
                                                     uu____3063
                                                    in
                                                 let uu____3064 =
                                                   __apply uopt tm' typ'  in
                                                 bind uu____3064
                                                   (fun uu____3072  ->
                                                      let u1 =
                                                        bnorm
                                                          goal.FStar_Tactics_Types.context
                                                          u
                                                         in
                                                      let uu____3074 =
                                                        let uu____3075 =
                                                          let uu____3078 =
                                                            let uu____3079 =
                                                              FStar_Syntax_Util.head_and_args
                                                                u1
                                                               in
                                                            FStar_Pervasives_Native.fst
                                                              uu____3079
                                                             in
                                                          FStar_Syntax_Subst.compress
                                                            uu____3078
                                                           in
                                                        uu____3075.FStar_Syntax_Syntax.n
                                                         in
                                                      match uu____3074 with
                                                      | FStar_Syntax_Syntax.Tm_uvar
                                                          (uvar,uu____3107)
                                                          ->
                                                          bind get
                                                            (fun ps  ->
                                                               let uu____3135
                                                                 =
                                                                 uopt &&
                                                                   (uvar_free
                                                                    uvar ps)
                                                                  in
                                                               if uu____3135
                                                               then ret ()
                                                               else
                                                                 (let uu____3139
                                                                    =
                                                                    let uu____3142
                                                                    =
                                                                    let uu___84_3143
                                                                    = goal
                                                                     in
                                                                    let uu____3144
                                                                    =
                                                                    bnorm
                                                                    goal.FStar_Tactics_Types.context
                                                                    u1  in
                                                                    let uu____3145
                                                                    =
                                                                    bnorm
                                                                    goal.FStar_Tactics_Types.context
                                                                    bv.FStar_Syntax_Syntax.sort
                                                                     in
                                                                    {
                                                                    FStar_Tactics_Types.context
                                                                    =
                                                                    (uu___84_3143.FStar_Tactics_Types.context);
                                                                    FStar_Tactics_Types.witness
                                                                    =
                                                                    uu____3144;
                                                                    FStar_Tactics_Types.goal_ty
                                                                    =
                                                                    uu____3145;
                                                                    FStar_Tactics_Types.opts
                                                                    =
                                                                    (uu___84_3143.FStar_Tactics_Types.opts);
                                                                    FStar_Tactics_Types.is_guard
                                                                    = false
                                                                    }  in
                                                                    [uu____3142]
                                                                     in
                                                                  add_goals
                                                                    uu____3139))
                                                      | t -> ret ()))))))))
  
let try_unif : 'a . 'a tac -> 'a tac -> 'a tac =
  fun t  ->
    fun t'  -> mk_tac (fun ps  -> try run t ps with | NoUnif  -> run t' ps)
  
let (apply : Prims.bool -> FStar_Syntax_Syntax.term -> Prims.unit tac) =
  fun uopt  ->
    fun tm  ->
      let uu____3191 =
        mlog
          (fun uu____3196  ->
             let uu____3197 = FStar_Syntax_Print.term_to_string tm  in
             FStar_Util.print1 "apply: tm = %s\n" uu____3197)
          (fun uu____3199  ->
             bind cur_goal
               (fun goal  ->
                  let uu____3203 = __tc goal.FStar_Tactics_Types.context tm
                     in
                  bind uu____3203
                    (fun uu____3224  ->
                       match uu____3224 with
                       | (tm1,typ,guard) ->
                           let uu____3236 =
                             let uu____3239 =
                               let uu____3242 = __apply uopt tm1 typ  in
                               bind uu____3242
                                 (fun uu____3246  ->
                                    add_goal_from_guard "apply guard"
                                      goal.FStar_Tactics_Types.context guard
                                      goal.FStar_Tactics_Types.opts)
                                in
                             focus uu____3239  in
                           let uu____3247 =
                             let uu____3250 =
                               tts goal.FStar_Tactics_Types.context tm1  in
                             let uu____3251 =
                               tts goal.FStar_Tactics_Types.context typ  in
                             let uu____3252 =
                               tts goal.FStar_Tactics_Types.context
                                 goal.FStar_Tactics_Types.goal_ty
                                in
                             fail3
                               "Cannot instantiate %s (of type %s) to match goal (%s)"
                               uu____3250 uu____3251 uu____3252
                              in
                           try_unif uu____3236 uu____3247)))
         in
      FStar_All.pipe_left (wrap_err "apply") uu____3191
  
let (apply_lemma : FStar_Syntax_Syntax.term -> Prims.unit tac) =
  fun tm  ->
    let uu____3264 =
      let uu____3267 =
        mlog
          (fun uu____3272  ->
             let uu____3273 = FStar_Syntax_Print.term_to_string tm  in
             FStar_Util.print1 "apply_lemma: tm = %s\n" uu____3273)
          (fun uu____3276  ->
             let is_unit_t t =
               let uu____3281 =
                 let uu____3282 = FStar_Syntax_Subst.compress t  in
                 uu____3282.FStar_Syntax_Syntax.n  in
               match uu____3281 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.unit_lid
                   -> true
               | uu____3286 -> false  in
             bind cur_goal
               (fun goal  ->
                  let uu____3290 = __tc goal.FStar_Tactics_Types.context tm
                     in
                  bind uu____3290
                    (fun uu____3312  ->
                       match uu____3312 with
                       | (tm1,t,guard) ->
                           let uu____3324 =
                             FStar_Syntax_Util.arrow_formals_comp t  in
                           (match uu____3324 with
                            | (bs,comp) ->
                                if
                                  Prims.op_Negation
                                    (FStar_Syntax_Util.is_lemma_comp comp)
                                then fail "not a lemma"
                                else
                                  (let uu____3354 =
                                     FStar_List.fold_left
                                       (fun uu____3400  ->
                                          fun uu____3401  ->
                                            match (uu____3400, uu____3401)
                                            with
                                            | ((uvs,guard1,subst1),(b,aq)) ->
                                                let b_t =
                                                  FStar_Syntax_Subst.subst
                                                    subst1
                                                    b.FStar_Syntax_Syntax.sort
                                                   in
                                                let uu____3504 =
                                                  is_unit_t b_t  in
                                                if uu____3504
                                                then
                                                  (((FStar_Syntax_Util.exp_unit,
                                                      aq) :: uvs), guard1,
                                                    ((FStar_Syntax_Syntax.NT
                                                        (b,
                                                          FStar_Syntax_Util.exp_unit))
                                                    :: subst1))
                                                else
                                                  (let uu____3542 =
                                                     FStar_TypeChecker_Util.new_implicit_var
                                                       "apply_lemma"
                                                       (goal.FStar_Tactics_Types.goal_ty).FStar_Syntax_Syntax.pos
                                                       goal.FStar_Tactics_Types.context
                                                       b_t
                                                      in
                                                   match uu____3542 with
                                                   | (u,uu____3572,g_u) ->
                                                       let uu____3586 =
                                                         FStar_TypeChecker_Rel.conj_guard
                                                           guard1 g_u
                                                          in
                                                       (((u, aq) :: uvs),
                                                         uu____3586,
                                                         ((FStar_Syntax_Syntax.NT
                                                             (b, u)) ::
                                                         subst1))))
                                       ([], guard, []) bs
                                      in
                                   match uu____3354 with
                                   | (uvs,implicits,subst1) ->
                                       let uvs1 = FStar_List.rev uvs  in
                                       let comp1 =
                                         FStar_Syntax_Subst.subst_comp subst1
                                           comp
                                          in
                                       let uu____3656 =
                                         let uu____3665 =
                                           let uu____3674 =
                                             FStar_Syntax_Util.comp_to_comp_typ
                                               comp1
                                              in
                                           uu____3674.FStar_Syntax_Syntax.effect_args
                                            in
                                         match uu____3665 with
                                         | pre::post::uu____3685 ->
                                             ((FStar_Pervasives_Native.fst
                                                 pre),
                                               (FStar_Pervasives_Native.fst
                                                  post))
                                         | uu____3726 ->
                                             failwith
                                               "apply_lemma: impossible: not a lemma"
                                          in
                                       (match uu____3656 with
                                        | (pre,post) ->
                                            let post1 =
                                              let uu____3758 =
                                                let uu____3767 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    FStar_Syntax_Util.exp_unit
                                                   in
                                                [uu____3767]  in
                                              FStar_Syntax_Util.mk_app post
                                                uu____3758
                                               in
                                            let uu____3768 =
                                              let uu____3769 =
                                                let uu____3770 =
                                                  FStar_Syntax_Util.mk_squash
                                                    FStar_Syntax_Syntax.U_zero
                                                    post1
                                                   in
                                                do_unify
                                                  goal.FStar_Tactics_Types.context
                                                  uu____3770
                                                  goal.FStar_Tactics_Types.goal_ty
                                                 in
                                              Prims.op_Negation uu____3769
                                               in
                                            if uu____3768
                                            then
                                              let uu____3773 =
                                                tts
                                                  goal.FStar_Tactics_Types.context
                                                  tm1
                                                 in
                                              let uu____3774 =
                                                let uu____3775 =
                                                  FStar_Syntax_Util.mk_squash
                                                    FStar_Syntax_Syntax.U_zero
                                                    post1
                                                   in
                                                tts
                                                  goal.FStar_Tactics_Types.context
                                                  uu____3775
                                                 in
                                              let uu____3776 =
                                                tts
                                                  goal.FStar_Tactics_Types.context
                                                  goal.FStar_Tactics_Types.goal_ty
                                                 in
                                              fail3
                                                "Cannot instantiate lemma %s (with postcondition: %s) to match goal (%s)"
                                                uu____3773 uu____3774
                                                uu____3776
                                            else
                                              (let uu____3778 =
                                                 add_implicits
                                                   implicits.FStar_TypeChecker_Env.implicits
                                                  in
                                               bind uu____3778
                                                 (fun uu____3783  ->
                                                    let uu____3784 =
                                                      solve goal
                                                        FStar_Syntax_Util.exp_unit
                                                       in
                                                    bind uu____3784
                                                      (fun uu____3792  ->
                                                         let is_free_uvar uv
                                                           t1 =
                                                           let free_uvars =
                                                             let uu____3803 =
                                                               let uu____3810
                                                                 =
                                                                 FStar_Syntax_Free.uvars
                                                                   t1
                                                                  in
                                                               FStar_Util.set_elements
                                                                 uu____3810
                                                                in
                                                             FStar_List.map
                                                               FStar_Pervasives_Native.fst
                                                               uu____3803
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
                                                           let uu____3851 =
                                                             FStar_Syntax_Util.head_and_args
                                                               t1
                                                              in
                                                           match uu____3851
                                                           with
                                                           | (hd1,uu____3867)
                                                               ->
                                                               (match 
                                                                  hd1.FStar_Syntax_Syntax.n
                                                                with
                                                                | FStar_Syntax_Syntax.Tm_uvar
                                                                    (uv,uu____3889)
                                                                    ->
                                                                    appears
                                                                    uv goals
                                                                | uu____3914
                                                                    -> false)
                                                            in
                                                         let uu____3915 =
                                                           FStar_All.pipe_right
                                                             implicits.FStar_TypeChecker_Env.implicits
                                                             (mapM
                                                                (fun
                                                                   uu____3987
                                                                    ->
                                                                   match uu____3987
                                                                   with
                                                                   | 
                                                                   (_msg,env,_uvar,term,typ,uu____4015)
                                                                    ->
                                                                    let uu____4016
                                                                    =
                                                                    FStar_Syntax_Util.head_and_args
                                                                    term  in
                                                                    (match uu____4016
                                                                    with
                                                                    | 
                                                                    (hd1,uu____4042)
                                                                    ->
                                                                    let uu____4063
                                                                    =
                                                                    let uu____4064
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    hd1  in
                                                                    uu____4064.FStar_Syntax_Syntax.n
                                                                     in
                                                                    (match uu____4063
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Tm_uvar
                                                                    uu____4077
                                                                    ->
                                                                    let uu____4094
                                                                    =
                                                                    let uu____4103
                                                                    =
                                                                    let uu____4106
                                                                    =
                                                                    let uu___87_4107
                                                                    = goal
                                                                     in
                                                                    let uu____4108
                                                                    =
                                                                    bnorm
                                                                    goal.FStar_Tactics_Types.context
                                                                    term  in
                                                                    let uu____4109
                                                                    =
                                                                    bnorm
                                                                    goal.FStar_Tactics_Types.context
                                                                    typ  in
                                                                    {
                                                                    FStar_Tactics_Types.context
                                                                    =
                                                                    (uu___87_4107.FStar_Tactics_Types.context);
                                                                    FStar_Tactics_Types.witness
                                                                    =
                                                                    uu____4108;
                                                                    FStar_Tactics_Types.goal_ty
                                                                    =
                                                                    uu____4109;
                                                                    FStar_Tactics_Types.opts
                                                                    =
                                                                    (uu___87_4107.FStar_Tactics_Types.opts);
                                                                    FStar_Tactics_Types.is_guard
                                                                    =
                                                                    (uu___87_4107.FStar_Tactics_Types.is_guard)
                                                                    }  in
                                                                    [uu____4106]
                                                                     in
                                                                    (uu____4103,
                                                                    [])  in
                                                                    ret
                                                                    uu____4094
                                                                    | 
                                                                    uu____4122
                                                                    ->
                                                                    let g_typ
                                                                    =
                                                                    let uu____4124
                                                                    =
                                                                    FStar_Options.__temp_fast_implicits
                                                                    ()  in
                                                                    if
                                                                    uu____4124
                                                                    then
                                                                    FStar_TypeChecker_TcTerm.check_type_of_well_typed_term
                                                                    false env
                                                                    term typ
                                                                    else
                                                                    (let term1
                                                                    =
                                                                    bnorm env
                                                                    term  in
                                                                    let uu____4127
                                                                    =
                                                                    let uu____4134
                                                                    =
                                                                    FStar_TypeChecker_Env.set_expected_typ
                                                                    env typ
                                                                     in
                                                                    env.FStar_TypeChecker_Env.type_of
                                                                    uu____4134
                                                                    term1  in
                                                                    match uu____4127
                                                                    with
                                                                    | 
                                                                    (uu____4135,uu____4136,g_typ)
                                                                    -> g_typ)
                                                                     in
                                                                    let uu____4138
                                                                    =
                                                                    goal_from_guard
                                                                    "apply_lemma solved arg"
                                                                    goal.FStar_Tactics_Types.context
                                                                    g_typ
                                                                    goal.FStar_Tactics_Types.opts
                                                                     in
                                                                    bind
                                                                    uu____4138
                                                                    (fun
                                                                    uu___58_4154
                                                                     ->
                                                                    match uu___58_4154
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
                                                         bind uu____3915
                                                           (fun goals_  ->
                                                              let sub_goals =
                                                                let uu____4222
                                                                  =
                                                                  FStar_List.map
                                                                    FStar_Pervasives_Native.fst
                                                                    goals_
                                                                   in
                                                                FStar_List.flatten
                                                                  uu____4222
                                                                 in
                                                              let smt_goals =
                                                                let uu____4244
                                                                  =
                                                                  FStar_List.map
                                                                    FStar_Pervasives_Native.snd
                                                                    goals_
                                                                   in
                                                                FStar_List.flatten
                                                                  uu____4244
                                                                 in
                                                              let rec filter'
                                                                a f xs =
                                                                match xs with
                                                                | [] -> []
                                                                | x::xs1 ->
                                                                    let uu____4299
                                                                    = f x xs1
                                                                     in
                                                                    if
                                                                    uu____4299
                                                                    then
                                                                    let uu____4302
                                                                    =
                                                                    filter'
                                                                    () f xs1
                                                                     in x ::
                                                                    uu____4302
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
                                                                    let uu____4316
                                                                    =
                                                                    checkone
                                                                    g.FStar_Tactics_Types.witness
                                                                    goals  in
                                                                    Prims.op_Negation
                                                                    uu____4316))
                                                                    a438 a439)
                                                                    (Obj.magic
                                                                    sub_goals))
                                                                 in
                                                              let uu____4317
                                                                =
                                                                add_goal_from_guard
                                                                  "apply_lemma guard"
                                                                  goal.FStar_Tactics_Types.context
                                                                  guard
                                                                  goal.FStar_Tactics_Types.opts
                                                                 in
                                                              bind uu____4317
                                                                (fun
                                                                   uu____4322
                                                                    ->
                                                                   let uu____4323
                                                                    =
                                                                    let uu____4326
                                                                    =
                                                                    let uu____4327
                                                                    =
                                                                    let uu____4328
                                                                    =
                                                                    FStar_Syntax_Util.mk_squash
                                                                    FStar_Syntax_Syntax.U_zero
                                                                    pre  in
                                                                    istrivial
                                                                    goal.FStar_Tactics_Types.context
                                                                    uu____4328
                                                                     in
                                                                    Prims.op_Negation
                                                                    uu____4327
                                                                     in
                                                                    if
                                                                    uu____4326
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
                                                                    uu____4323
                                                                    (fun
                                                                    uu____4334
                                                                     ->
                                                                    let uu____4335
                                                                    =
                                                                    add_smt_goals
                                                                    smt_goals
                                                                     in
                                                                    bind
                                                                    uu____4335
                                                                    (fun
                                                                    uu____4339
                                                                     ->
                                                                    add_goals
                                                                    sub_goals1)))))))))))))
         in
      focus uu____3267  in
    FStar_All.pipe_left (wrap_err "apply_lemma") uu____3264
  
let (destruct_eq' :
  FStar_Syntax_Syntax.typ ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun typ  ->
    let uu____4359 = FStar_Syntax_Util.destruct_typ_as_formula typ  in
    match uu____4359 with
    | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn
        (l,uu____4369::(e1,uu____4371)::(e2,uu____4373)::[])) when
        FStar_Ident.lid_equals l FStar_Parser_Const.eq2_lid ->
        FStar_Pervasives_Native.Some (e1, e2)
    | uu____4432 -> FStar_Pervasives_Native.None
  
let (destruct_eq :
  FStar_Syntax_Syntax.typ ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun typ  ->
    let uu____4454 = destruct_eq' typ  in
    match uu____4454 with
    | FStar_Pervasives_Native.Some t -> FStar_Pervasives_Native.Some t
    | FStar_Pervasives_Native.None  ->
        let uu____4484 = FStar_Syntax_Util.un_squash typ  in
        (match uu____4484 with
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
        let uu____4540 = FStar_TypeChecker_Env.pop_bv e1  in
        match uu____4540 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (bv',e') ->
            if FStar_Syntax_Syntax.bv_eq bvar bv'
            then FStar_Pervasives_Native.Some (e', [])
            else
              (let uu____4588 = aux e'  in
               FStar_Util.map_opt uu____4588
                 (fun uu____4612  ->
                    match uu____4612 with | (e'',bvs) -> (e'', (bv' :: bvs))))
         in
      let uu____4633 = aux e  in
      FStar_Util.map_opt uu____4633
        (fun uu____4657  ->
           match uu____4657 with | (e',bvs) -> (e', (FStar_List.rev bvs)))
  
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
          let uu____4712 = split_env b1 g.FStar_Tactics_Types.context  in
          FStar_Util.map_opt uu____4712
            (fun uu____4736  ->
               match uu____4736 with
               | (e0,bvs) ->
                   let s1 bv =
                     let uu___88_4753 = bv  in
                     let uu____4754 =
                       FStar_Syntax_Subst.subst s bv.FStar_Syntax_Syntax.sort
                        in
                     {
                       FStar_Syntax_Syntax.ppname =
                         (uu___88_4753.FStar_Syntax_Syntax.ppname);
                       FStar_Syntax_Syntax.index =
                         (uu___88_4753.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort = uu____4754
                     }  in
                   let bvs1 = FStar_List.map s1 bvs  in
                   let c = push_bvs e0 (b2 :: bvs1)  in
                   let w =
                     FStar_Syntax_Subst.subst s g.FStar_Tactics_Types.witness
                      in
                   let t =
                     FStar_Syntax_Subst.subst s g.FStar_Tactics_Types.goal_ty
                      in
                   let uu___89_4763 = g  in
                   {
                     FStar_Tactics_Types.context = c;
                     FStar_Tactics_Types.witness = w;
                     FStar_Tactics_Types.goal_ty = t;
                     FStar_Tactics_Types.opts =
                       (uu___89_4763.FStar_Tactics_Types.opts);
                     FStar_Tactics_Types.is_guard =
                       (uu___89_4763.FStar_Tactics_Types.is_guard)
                   })
  
let (rewrite : FStar_Syntax_Syntax.binder -> Prims.unit tac) =
  fun h  ->
    bind cur_goal
      (fun goal  ->
         let uu____4776 = h  in
         match uu____4776 with
         | (bv,uu____4780) ->
             mlog
               (fun uu____4784  ->
                  let uu____4785 = FStar_Syntax_Print.bv_to_string bv  in
                  let uu____4786 =
                    tts goal.FStar_Tactics_Types.context
                      bv.FStar_Syntax_Syntax.sort
                     in
                  FStar_Util.print2 "+++Rewrite %s : %s\n" uu____4785
                    uu____4786)
               (fun uu____4789  ->
                  let uu____4790 =
                    split_env bv goal.FStar_Tactics_Types.context  in
                  match uu____4790 with
                  | FStar_Pervasives_Native.None  ->
                      fail "rewrite: binder not found in environment"
                  | FStar_Pervasives_Native.Some (e0,bvs) ->
                      let uu____4819 =
                        destruct_eq bv.FStar_Syntax_Syntax.sort  in
                      (match uu____4819 with
                       | FStar_Pervasives_Native.Some (x,e) ->
                           let uu____4834 =
                             let uu____4835 = FStar_Syntax_Subst.compress x
                                in
                             uu____4835.FStar_Syntax_Syntax.n  in
                           (match uu____4834 with
                            | FStar_Syntax_Syntax.Tm_name x1 ->
                                let s = [FStar_Syntax_Syntax.NT (x1, e)]  in
                                let s1 bv1 =
                                  let uu___90_4848 = bv1  in
                                  let uu____4849 =
                                    FStar_Syntax_Subst.subst s
                                      bv1.FStar_Syntax_Syntax.sort
                                     in
                                  {
                                    FStar_Syntax_Syntax.ppname =
                                      (uu___90_4848.FStar_Syntax_Syntax.ppname);
                                    FStar_Syntax_Syntax.index =
                                      (uu___90_4848.FStar_Syntax_Syntax.index);
                                    FStar_Syntax_Syntax.sort = uu____4849
                                  }  in
                                let bvs1 = FStar_List.map s1 bvs  in
                                let uu____4855 =
                                  let uu___91_4856 = goal  in
                                  let uu____4857 = push_bvs e0 (bv :: bvs1)
                                     in
                                  let uu____4858 =
                                    FStar_Syntax_Subst.subst s
                                      goal.FStar_Tactics_Types.witness
                                     in
                                  let uu____4859 =
                                    FStar_Syntax_Subst.subst s
                                      goal.FStar_Tactics_Types.goal_ty
                                     in
                                  {
                                    FStar_Tactics_Types.context = uu____4857;
                                    FStar_Tactics_Types.witness = uu____4858;
                                    FStar_Tactics_Types.goal_ty = uu____4859;
                                    FStar_Tactics_Types.opts =
                                      (uu___91_4856.FStar_Tactics_Types.opts);
                                    FStar_Tactics_Types.is_guard =
                                      (uu___91_4856.FStar_Tactics_Types.is_guard)
                                  }  in
                                replace_cur uu____4855
                            | uu____4860 ->
                                fail
                                  "rewrite: Not an equality hypothesis with a variable on the LHS")
                       | uu____4861 ->
                           fail "rewrite: Not an equality hypothesis")))
  
let (rename_to :
  FStar_Syntax_Syntax.binder -> Prims.string -> Prims.unit tac) =
  fun b  ->
    fun s  ->
      bind cur_goal
        (fun goal  ->
           let uu____4886 = b  in
           match uu____4886 with
           | (bv,uu____4890) ->
               let bv' =
                 FStar_Syntax_Syntax.freshen_bv
                   (let uu___92_4894 = bv  in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (FStar_Ident.mk_ident
                           (s,
                             ((bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange)));
                      FStar_Syntax_Syntax.index =
                        (uu___92_4894.FStar_Syntax_Syntax.index);
                      FStar_Syntax_Syntax.sort =
                        (uu___92_4894.FStar_Syntax_Syntax.sort)
                    })
                  in
               let s1 =
                 let uu____4898 =
                   let uu____4899 =
                     let uu____4906 = FStar_Syntax_Syntax.bv_to_name bv'  in
                     (bv, uu____4906)  in
                   FStar_Syntax_Syntax.NT uu____4899  in
                 [uu____4898]  in
               let uu____4907 = subst_goal bv bv' s1 goal  in
               (match uu____4907 with
                | FStar_Pervasives_Native.None  ->
                    fail "rename_to: binder not found in environment"
                | FStar_Pervasives_Native.Some goal1 -> replace_cur goal1))
  
let (binder_retype : FStar_Syntax_Syntax.binder -> Prims.unit tac) =
  fun b  ->
    bind cur_goal
      (fun goal  ->
         let uu____4926 = b  in
         match uu____4926 with
         | (bv,uu____4930) ->
             let uu____4931 = split_env bv goal.FStar_Tactics_Types.context
                in
             (match uu____4931 with
              | FStar_Pervasives_Native.None  ->
                  fail "binder_retype: binder is not present in environment"
              | FStar_Pervasives_Native.Some (e0,bvs) ->
                  let uu____4960 = FStar_Syntax_Util.type_u ()  in
                  (match uu____4960 with
                   | (ty,u) ->
                       let uu____4969 = new_uvar "binder_retype" e0 ty  in
                       bind uu____4969
                         (fun t'  ->
                            let bv'' =
                              let uu___93_4979 = bv  in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___93_4979.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___93_4979.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = t'
                              }  in
                            let s =
                              let uu____4983 =
                                let uu____4984 =
                                  let uu____4991 =
                                    FStar_Syntax_Syntax.bv_to_name bv''  in
                                  (bv, uu____4991)  in
                                FStar_Syntax_Syntax.NT uu____4984  in
                              [uu____4983]  in
                            let bvs1 =
                              FStar_List.map
                                (fun b1  ->
                                   let uu___94_4999 = b1  in
                                   let uu____5000 =
                                     FStar_Syntax_Subst.subst s
                                       b1.FStar_Syntax_Syntax.sort
                                      in
                                   {
                                     FStar_Syntax_Syntax.ppname =
                                       (uu___94_4999.FStar_Syntax_Syntax.ppname);
                                     FStar_Syntax_Syntax.index =
                                       (uu___94_4999.FStar_Syntax_Syntax.index);
                                     FStar_Syntax_Syntax.sort = uu____5000
                                   }) bvs
                               in
                            let env' = push_bvs e0 (bv'' :: bvs1)  in
                            bind dismiss
                              (fun uu____5006  ->
                                 let uu____5007 =
                                   let uu____5010 =
                                     let uu____5013 =
                                       let uu___95_5014 = goal  in
                                       let uu____5015 =
                                         FStar_Syntax_Subst.subst s
                                           goal.FStar_Tactics_Types.witness
                                          in
                                       let uu____5016 =
                                         FStar_Syntax_Subst.subst s
                                           goal.FStar_Tactics_Types.goal_ty
                                          in
                                       {
                                         FStar_Tactics_Types.context = env';
                                         FStar_Tactics_Types.witness =
                                           uu____5015;
                                         FStar_Tactics_Types.goal_ty =
                                           uu____5016;
                                         FStar_Tactics_Types.opts =
                                           (uu___95_5014.FStar_Tactics_Types.opts);
                                         FStar_Tactics_Types.is_guard =
                                           (uu___95_5014.FStar_Tactics_Types.is_guard)
                                       }  in
                                     [uu____5013]  in
                                   add_goals uu____5010  in
                                 bind uu____5007
                                   (fun uu____5019  ->
                                      let uu____5020 =
                                        FStar_Syntax_Util.mk_eq2
                                          (FStar_Syntax_Syntax.U_succ u) ty
                                          bv.FStar_Syntax_Syntax.sort t'
                                         in
                                      add_irrelevant_goal
                                        "binder_retype equation" e0
                                        uu____5020
                                        goal.FStar_Tactics_Types.opts))))))
  
let (norm_binder_type :
  FStar_Syntax_Embeddings.norm_step Prims.list ->
    FStar_Syntax_Syntax.binder -> Prims.unit tac)
  =
  fun s  ->
    fun b  ->
      bind cur_goal
        (fun goal  ->
           let uu____5041 = b  in
           match uu____5041 with
           | (bv,uu____5045) ->
               let uu____5046 = split_env bv goal.FStar_Tactics_Types.context
                  in
               (match uu____5046 with
                | FStar_Pervasives_Native.None  ->
                    fail
                      "binder_retype: binder is not present in environment"
                | FStar_Pervasives_Native.Some (e0,bvs) ->
                    let steps =
                      let uu____5078 =
                        FStar_TypeChecker_Normalize.tr_norm_steps s  in
                      FStar_List.append
                        [FStar_TypeChecker_Normalize.Reify;
                        FStar_TypeChecker_Normalize.UnfoldTac] uu____5078
                       in
                    let sort' =
                      normalize steps e0 bv.FStar_Syntax_Syntax.sort  in
                    let bv' =
                      let uu___96_5083 = bv  in
                      {
                        FStar_Syntax_Syntax.ppname =
                          (uu___96_5083.FStar_Syntax_Syntax.ppname);
                        FStar_Syntax_Syntax.index =
                          (uu___96_5083.FStar_Syntax_Syntax.index);
                        FStar_Syntax_Syntax.sort = sort'
                      }  in
                    let env' = push_bvs e0 (bv' :: bvs)  in
                    replace_cur
                      (let uu___97_5087 = goal  in
                       {
                         FStar_Tactics_Types.context = env';
                         FStar_Tactics_Types.witness =
                           (uu___97_5087.FStar_Tactics_Types.witness);
                         FStar_Tactics_Types.goal_ty =
                           (uu___97_5087.FStar_Tactics_Types.goal_ty);
                         FStar_Tactics_Types.opts =
                           (uu___97_5087.FStar_Tactics_Types.opts);
                         FStar_Tactics_Types.is_guard =
                           (uu___97_5087.FStar_Tactics_Types.is_guard)
                       })))
  
let (revert : Prims.unit tac) =
  bind cur_goal
    (fun goal  ->
       let uu____5095 =
         FStar_TypeChecker_Env.pop_bv goal.FStar_Tactics_Types.context  in
       match uu____5095 with
       | FStar_Pervasives_Native.None  -> fail "Cannot revert; empty context"
       | FStar_Pervasives_Native.Some (x,env') ->
           let typ' =
             let uu____5117 =
               FStar_Syntax_Syntax.mk_Total goal.FStar_Tactics_Types.goal_ty
                in
             FStar_Syntax_Util.arrow [(x, FStar_Pervasives_Native.None)]
               uu____5117
              in
           let w' =
             FStar_Syntax_Util.abs [(x, FStar_Pervasives_Native.None)]
               goal.FStar_Tactics_Types.witness FStar_Pervasives_Native.None
              in
           replace_cur
             (let uu___98_5151 = goal  in
              {
                FStar_Tactics_Types.context = env';
                FStar_Tactics_Types.witness = w';
                FStar_Tactics_Types.goal_ty = typ';
                FStar_Tactics_Types.opts =
                  (uu___98_5151.FStar_Tactics_Types.opts);
                FStar_Tactics_Types.is_guard =
                  (uu___98_5151.FStar_Tactics_Types.is_guard)
              }))
  
let (free_in :
  FStar_Syntax_Syntax.bv -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun bv  ->
    fun t  ->
      let uu____5158 = FStar_Syntax_Free.names t  in
      FStar_Util.set_mem bv uu____5158
  
let rec (clear : FStar_Syntax_Syntax.binder -> Prims.unit tac) =
  fun b  ->
    let bv = FStar_Pervasives_Native.fst b  in
    bind cur_goal
      (fun goal  ->
         mlog
           (fun uu____5174  ->
              let uu____5175 = FStar_Syntax_Print.binder_to_string b  in
              let uu____5176 =
                let uu____5177 =
                  let uu____5178 =
                    FStar_TypeChecker_Env.all_binders
                      goal.FStar_Tactics_Types.context
                     in
                  FStar_All.pipe_right uu____5178 FStar_List.length  in
                FStar_All.pipe_right uu____5177 FStar_Util.string_of_int  in
              FStar_Util.print2 "Clear of (%s), env has %s binders\n"
                uu____5175 uu____5176)
           (fun uu____5189  ->
              let uu____5190 = split_env bv goal.FStar_Tactics_Types.context
                 in
              match uu____5190 with
              | FStar_Pervasives_Native.None  ->
                  fail "Cannot clear; binder not in environment"
              | FStar_Pervasives_Native.Some (e',bvs) ->
                  let rec check bvs1 =
                    match bvs1 with
                    | [] -> ret ()
                    | bv'::bvs2 ->
                        let uu____5235 =
                          free_in bv bv'.FStar_Syntax_Syntax.sort  in
                        if uu____5235
                        then
                          let uu____5238 =
                            let uu____5239 =
                              FStar_Syntax_Print.bv_to_string bv'  in
                            FStar_Util.format1
                              "Cannot clear; binder present in the type of %s"
                              uu____5239
                             in
                          fail uu____5238
                        else check bvs2
                     in
                  let uu____5241 =
                    free_in bv goal.FStar_Tactics_Types.goal_ty  in
                  if uu____5241
                  then fail "Cannot clear; binder present in goal"
                  else
                    (let uu____5245 = check bvs  in
                     bind uu____5245
                       (fun uu____5251  ->
                          let env' = push_bvs e' bvs  in
                          let uu____5253 =
                            new_uvar "clear.witness" env'
                              goal.FStar_Tactics_Types.goal_ty
                             in
                          bind uu____5253
                            (fun ut  ->
                               let uu____5259 =
                                 do_unify goal.FStar_Tactics_Types.context
                                   goal.FStar_Tactics_Types.witness ut
                                  in
                               if uu____5259
                               then
                                 replace_cur
                                   (let uu___99_5264 = goal  in
                                    {
                                      FStar_Tactics_Types.context = env';
                                      FStar_Tactics_Types.witness = ut;
                                      FStar_Tactics_Types.goal_ty =
                                        (uu___99_5264.FStar_Tactics_Types.goal_ty);
                                      FStar_Tactics_Types.opts =
                                        (uu___99_5264.FStar_Tactics_Types.opts);
                                      FStar_Tactics_Types.is_guard =
                                        (uu___99_5264.FStar_Tactics_Types.is_guard)
                                    })
                               else
                                 fail
                                   "Cannot clear; binder appears in witness")))))
  
let (clear_top : Prims.unit tac) =
  bind cur_goal
    (fun goal  ->
       let uu____5273 =
         FStar_TypeChecker_Env.pop_bv goal.FStar_Tactics_Types.context  in
       match uu____5273 with
       | FStar_Pervasives_Native.None  -> fail "Cannot clear; empty context"
       | FStar_Pervasives_Native.Some (x,uu____5287) ->
           let uu____5292 = FStar_Syntax_Syntax.mk_binder x  in
           clear uu____5292)
  
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
           let uu___100_5308 = g  in
           {
             FStar_Tactics_Types.context = ctx';
             FStar_Tactics_Types.witness =
               (uu___100_5308.FStar_Tactics_Types.witness);
             FStar_Tactics_Types.goal_ty =
               (uu___100_5308.FStar_Tactics_Types.goal_ty);
             FStar_Tactics_Types.opts =
               (uu___100_5308.FStar_Tactics_Types.opts);
             FStar_Tactics_Types.is_guard =
               (uu___100_5308.FStar_Tactics_Types.is_guard)
           }  in
         bind dismiss (fun uu____5310  -> add_goals [g']))
  
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
           let uu___101_5326 = g  in
           {
             FStar_Tactics_Types.context = ctx';
             FStar_Tactics_Types.witness =
               (uu___101_5326.FStar_Tactics_Types.witness);
             FStar_Tactics_Types.goal_ty =
               (uu___101_5326.FStar_Tactics_Types.goal_ty);
             FStar_Tactics_Types.opts =
               (uu___101_5326.FStar_Tactics_Types.opts);
             FStar_Tactics_Types.is_guard =
               (uu___101_5326.FStar_Tactics_Types.is_guard)
           }  in
         bind dismiss (fun uu____5328  -> add_goals [g']))
  
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
            let uu____5360 = FStar_Syntax_Subst.compress t  in
            uu____5360.FStar_Syntax_Syntax.n  in
          let uu____5363 =
            if d = FStar_Tactics_Types.TopDown
            then
              f env
                (let uu___103_5369 = t  in
                 {
                   FStar_Syntax_Syntax.n = tn;
                   FStar_Syntax_Syntax.pos =
                     (uu___103_5369.FStar_Syntax_Syntax.pos);
                   FStar_Syntax_Syntax.vars =
                     (uu___103_5369.FStar_Syntax_Syntax.vars)
                 })
            else ret t  in
          bind uu____5363
            (fun t1  ->
               let tn1 =
                 let uu____5377 =
                   let uu____5378 = FStar_Syntax_Subst.compress t1  in
                   uu____5378.FStar_Syntax_Syntax.n  in
                 match uu____5377 with
                 | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
                     let ff = tac_fold_env d f env  in
                     let uu____5410 = ff hd1  in
                     bind uu____5410
                       (fun hd2  ->
                          let fa uu____5430 =
                            match uu____5430 with
                            | (a,q) ->
                                let uu____5443 = ff a  in
                                bind uu____5443 (fun a1  -> ret (a1, q))
                             in
                          let uu____5456 = mapM fa args  in
                          bind uu____5456
                            (fun args1  ->
                               ret (FStar_Syntax_Syntax.Tm_app (hd2, args1))))
                 | FStar_Syntax_Syntax.Tm_abs (bs,t2,k) ->
                     let uu____5516 = FStar_Syntax_Subst.open_term bs t2  in
                     (match uu____5516 with
                      | (bs1,t') ->
                          let uu____5525 =
                            let uu____5528 =
                              FStar_TypeChecker_Env.push_binders env bs1  in
                            tac_fold_env d f uu____5528 t'  in
                          bind uu____5525
                            (fun t''  ->
                               let uu____5532 =
                                 let uu____5533 =
                                   let uu____5550 =
                                     FStar_Syntax_Subst.close_binders bs1  in
                                   let uu____5551 =
                                     FStar_Syntax_Subst.close bs1 t''  in
                                   (uu____5550, uu____5551, k)  in
                                 FStar_Syntax_Syntax.Tm_abs uu____5533  in
                               ret uu____5532))
                 | FStar_Syntax_Syntax.Tm_arrow (bs,k) -> ret tn
                 | uu____5572 -> ret tn  in
               bind tn1
                 (fun tn2  ->
                    let t' =
                      let uu___102_5579 = t1  in
                      {
                        FStar_Syntax_Syntax.n = tn2;
                        FStar_Syntax_Syntax.pos =
                          (uu___102_5579.FStar_Syntax_Syntax.pos);
                        FStar_Syntax_Syntax.vars =
                          (uu___102_5579.FStar_Syntax_Syntax.vars)
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
            let uu____5608 = FStar_TypeChecker_TcTerm.tc_term env t  in
            match uu____5608 with
            | (t1,lcomp,g) ->
                let uu____5620 =
                  (let uu____5623 =
                     FStar_Syntax_Util.is_pure_or_ghost_lcomp lcomp  in
                   Prims.op_Negation uu____5623) ||
                    (let uu____5625 = FStar_TypeChecker_Rel.is_trivial g  in
                     Prims.op_Negation uu____5625)
                   in
                if uu____5620
                then ret t1
                else
                  (let rewrite_eq =
                     let typ = lcomp.FStar_Syntax_Syntax.res_typ  in
                     let uu____5635 = new_uvar "pointwise_rec" env typ  in
                     bind uu____5635
                       (fun ut  ->
                          log ps
                            (fun uu____5646  ->
                               let uu____5647 =
                                 FStar_Syntax_Print.term_to_string t1  in
                               let uu____5648 =
                                 FStar_Syntax_Print.term_to_string ut  in
                               FStar_Util.print2
                                 "Pointwise_rec: making equality\n\t%s ==\n\t%s\n"
                                 uu____5647 uu____5648);
                          (let uu____5649 =
                             let uu____5652 =
                               let uu____5653 =
                                 FStar_TypeChecker_TcTerm.universe_of env typ
                                  in
                               FStar_Syntax_Util.mk_eq2 uu____5653 typ t1 ut
                                in
                             add_irrelevant_goal "pointwise_rec equation" env
                               uu____5652 opts
                              in
                           bind uu____5649
                             (fun uu____5656  ->
                                let uu____5657 =
                                  bind tau
                                    (fun uu____5663  ->
                                       let ut1 =
                                         FStar_TypeChecker_Normalize.reduce_uvar_solutions
                                           env ut
                                          in
                                       log ps
                                         (fun uu____5669  ->
                                            let uu____5670 =
                                              FStar_Syntax_Print.term_to_string
                                                t1
                                               in
                                            let uu____5671 =
                                              FStar_Syntax_Print.term_to_string
                                                ut1
                                               in
                                            FStar_Util.print2
                                              "Pointwise_rec: succeeded rewriting\n\t%s to\n\t%s\n"
                                              uu____5670 uu____5671);
                                       ret ut1)
                                   in
                                focus uu____5657)))
                      in
                   let uu____5672 = trytac' rewrite_eq  in
                   bind uu____5672
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
          let uu____5820 = FStar_Syntax_Subst.compress t  in
          maybe_continue ctrl uu____5820
            (fun t1  ->
               let uu____5824 =
                 f env
                   (let uu___106_5833 = t1  in
                    {
                      FStar_Syntax_Syntax.n = (t1.FStar_Syntax_Syntax.n);
                      FStar_Syntax_Syntax.pos =
                        (uu___106_5833.FStar_Syntax_Syntax.pos);
                      FStar_Syntax_Syntax.vars =
                        (uu___106_5833.FStar_Syntax_Syntax.vars)
                    })
                  in
               bind uu____5824
                 (fun uu____5845  ->
                    match uu____5845 with
                    | (t2,ctrl1) ->
                        maybe_continue ctrl1 t2
                          (fun t3  ->
                             let uu____5864 =
                               let uu____5865 =
                                 FStar_Syntax_Subst.compress t3  in
                               uu____5865.FStar_Syntax_Syntax.n  in
                             match uu____5864 with
                             | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
                                 let uu____5898 =
                                   ctrl_tac_fold f env ctrl1 hd1  in
                                 bind uu____5898
                                   (fun uu____5923  ->
                                      match uu____5923 with
                                      | (hd2,ctrl2) ->
                                          let ctrl3 = keep_going ctrl2  in
                                          let uu____5939 =
                                            ctrl_tac_fold_args f env ctrl3
                                              args
                                             in
                                          bind uu____5939
                                            (fun uu____5966  ->
                                               match uu____5966 with
                                               | (args1,ctrl4) ->
                                                   ret
                                                     ((let uu___104_5996 = t3
                                                          in
                                                       {
                                                         FStar_Syntax_Syntax.n
                                                           =
                                                           (FStar_Syntax_Syntax.Tm_app
                                                              (hd2, args1));
                                                         FStar_Syntax_Syntax.pos
                                                           =
                                                           (uu___104_5996.FStar_Syntax_Syntax.pos);
                                                         FStar_Syntax_Syntax.vars
                                                           =
                                                           (uu___104_5996.FStar_Syntax_Syntax.vars)
                                                       }), ctrl4)))
                             | FStar_Syntax_Syntax.Tm_abs (bs,t4,k) ->
                                 let uu____6022 =
                                   FStar_Syntax_Subst.open_term bs t4  in
                                 (match uu____6022 with
                                  | (bs1,t') ->
                                      let uu____6037 =
                                        let uu____6044 =
                                          FStar_TypeChecker_Env.push_binders
                                            env bs1
                                           in
                                        ctrl_tac_fold f uu____6044 ctrl1 t'
                                         in
                                      bind uu____6037
                                        (fun uu____6062  ->
                                           match uu____6062 with
                                           | (t'',ctrl2) ->
                                               let uu____6077 =
                                                 let uu____6084 =
                                                   let uu___105_6087 = t4  in
                                                   let uu____6090 =
                                                     let uu____6091 =
                                                       let uu____6108 =
                                                         FStar_Syntax_Subst.close_binders
                                                           bs1
                                                          in
                                                       let uu____6109 =
                                                         FStar_Syntax_Subst.close
                                                           bs1 t''
                                                          in
                                                       (uu____6108,
                                                         uu____6109, k)
                                                        in
                                                     FStar_Syntax_Syntax.Tm_abs
                                                       uu____6091
                                                      in
                                                   {
                                                     FStar_Syntax_Syntax.n =
                                                       uu____6090;
                                                     FStar_Syntax_Syntax.pos
                                                       =
                                                       (uu___105_6087.FStar_Syntax_Syntax.pos);
                                                     FStar_Syntax_Syntax.vars
                                                       =
                                                       (uu___105_6087.FStar_Syntax_Syntax.vars)
                                                   }  in
                                                 (uu____6084, ctrl2)  in
                                               ret uu____6077))
                             | FStar_Syntax_Syntax.Tm_arrow (bs,k) ->
                                 ret (t3, ctrl1)
                             | uu____6142 -> ret (t3, ctrl1))))

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
              let uu____6193 = ctrl_tac_fold f env ctrl t  in
              bind uu____6193
                (fun uu____6221  ->
                   match uu____6221 with
                   | (t1,ctrl1) ->
                       let uu____6240 = ctrl_tac_fold_args f env ctrl1 ts1
                          in
                       bind uu____6240
                         (fun uu____6271  ->
                            match uu____6271 with
                            | (ts2,ctrl2) -> ret (((t1, q) :: ts2), ctrl2)))

let (rewrite_rec :
  FStar_Tactics_Types.proofstate ->
    rewrite_result ctrl_tac ->
      FStar_Options.optionstate ->
        FStar_TypeChecker_Env.env ->
          FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term ctrl_tac)
  =
  fun ps  ->
    fun maybe_rewrite  ->
      fun opts  ->
        fun env  ->
          fun t  ->
            let uu____6342 = FStar_TypeChecker_TcTerm.tc_term env t  in
            match uu____6342 with
            | (t1,lcomp,g) ->
                let uu____6354 =
                  (let uu____6357 =
                     FStar_Syntax_Util.is_pure_or_ghost_lcomp lcomp  in
                   Prims.op_Negation uu____6357) ||
                    (let uu____6359 = FStar_TypeChecker_Rel.is_trivial g  in
                     Prims.op_Negation uu____6359)
                   in
                if uu____6354
                then ret (t1, globalStop)
                else
                  (let typ = lcomp.FStar_Syntax_Syntax.res_typ  in
                   let uu____6370 = new_uvar_i "pointwise_rec" env typ  in
                   bind uu____6370
                     (fun uu____6390  ->
                        match uu____6390 with
                        | (ut,ut_imps) ->
                            (log ps
                               (fun uu____6407  ->
                                  let uu____6408 =
                                    FStar_Syntax_Print.term_to_string t1  in
                                  let uu____6409 =
                                    FStar_Syntax_Print.term_to_string ut  in
                                  FStar_Util.print2
                                    "Pointwise_rec: making equality\n\t%s ==\n\t%s\n"
                                    uu____6408 uu____6409);
                             (let uu____6410 =
                                let uu____6413 =
                                  let uu____6414 =
                                    FStar_TypeChecker_TcTerm.universe_of env
                                      typ
                                     in
                                  FStar_Syntax_Util.mk_eq2 uu____6414 typ t1
                                    ut
                                   in
                                add_irrelevant_goal "pointwise_rec equation"
                                  env uu____6413 opts
                                 in
                              bind uu____6410
                                (fun uu____6421  ->
                                   let uu____6422 =
                                     bind maybe_rewrite
                                       (fun uu____6442  ->
                                          match uu____6442 with
                                          | (res,ctrl) ->
                                              if res = skipThisTerm
                                              then
                                                bind dismiss
                                                  (fun uu____6467  ->
                                                     let uu____6468 =
                                                       remove_implicits
                                                         ut_imps
                                                        in
                                                     bind uu____6468
                                                       (fun uu____6476  ->
                                                          ret (t1, ctrl)))
                                              else
                                                (let ut1 =
                                                   FStar_TypeChecker_Normalize.reduce_uvar_solutions
                                                     env ut
                                                    in
                                                 log ps
                                                   (fun uu____6487  ->
                                                      let uu____6488 =
                                                        FStar_Syntax_Print.term_to_string
                                                          t1
                                                         in
                                                      let uu____6489 =
                                                        FStar_Syntax_Print.term_to_string
                                                          ut1
                                                         in
                                                      FStar_Util.print2
                                                        "Pointwise_rec: succeeded rewriting\n\t%s to\n\t%s\n"
                                                        uu____6488 uu____6489);
                                                 ret (ut1, ctrl)))
                                      in
                                   focus uu____6422)))))
  
let (topdown_rewrite :
  (Prims.bool,FStar_BigInt.t) FStar_Pervasives_Native.tuple2 tac ->
    Prims.unit tac)
  =
  fun tau  ->
    bind get
      (fun ps  ->
         let uu____6521 =
           match ps.FStar_Tactics_Types.goals with
           | g::gs -> (g, gs)
           | [] -> failwith "Pointwise: no goals"  in
         match uu____6521 with
         | (g,gs) ->
             let gt1 = g.FStar_Tactics_Types.goal_ty  in
             (log ps
                (fun uu____6558  ->
                   let uu____6559 = FStar_Syntax_Print.term_to_string gt1  in
                   FStar_Util.print1 "Pointwise starting with %s\n"
                     uu____6559);
              bind dismiss_all
                (fun uu____6562  ->
                   let uu____6563 =
                     ctrl_tac_fold
                       (rewrite_rec ps tau g.FStar_Tactics_Types.opts)
                       g.FStar_Tactics_Types.context keepGoing gt1
                      in
                   bind uu____6563
                     (fun uu____6581  ->
                        match uu____6581 with
                        | (gt',uu____6589) ->
                            (log ps
                               (fun uu____6593  ->
                                  let uu____6594 =
                                    FStar_Syntax_Print.term_to_string gt'  in
                                  FStar_Util.print1
                                    "Pointwise seems to have succeded with %s\n"
                                    uu____6594);
                             (let uu____6595 = push_goals gs  in
                              bind uu____6595
                                (fun uu____6599  ->
                                   add_goals
                                     [(let uu___107_6601 = g  in
                                       {
                                         FStar_Tactics_Types.context =
                                           (uu___107_6601.FStar_Tactics_Types.context);
                                         FStar_Tactics_Types.witness =
                                           (uu___107_6601.FStar_Tactics_Types.witness);
                                         FStar_Tactics_Types.goal_ty = gt';
                                         FStar_Tactics_Types.opts =
                                           (uu___107_6601.FStar_Tactics_Types.opts);
                                         FStar_Tactics_Types.is_guard =
                                           (uu___107_6601.FStar_Tactics_Types.is_guard)
                                       })])))))))
  
let (pointwise :
  FStar_Tactics_Types.direction -> Prims.unit tac -> Prims.unit tac) =
  fun d  ->
    fun tau  ->
      bind get
        (fun ps  ->
           let uu____6623 =
             match ps.FStar_Tactics_Types.goals with
             | g::gs -> (g, gs)
             | [] -> failwith "Pointwise: no goals"  in
           match uu____6623 with
           | (g,gs) ->
               let gt1 = g.FStar_Tactics_Types.goal_ty  in
               (log ps
                  (fun uu____6660  ->
                     let uu____6661 = FStar_Syntax_Print.term_to_string gt1
                        in
                     FStar_Util.print1 "Pointwise starting with %s\n"
                       uu____6661);
                bind dismiss_all
                  (fun uu____6664  ->
                     let uu____6665 =
                       tac_fold_env d
                         (pointwise_rec ps tau g.FStar_Tactics_Types.opts)
                         g.FStar_Tactics_Types.context gt1
                        in
                     bind uu____6665
                       (fun gt'  ->
                          log ps
                            (fun uu____6675  ->
                               let uu____6676 =
                                 FStar_Syntax_Print.term_to_string gt'  in
                               FStar_Util.print1
                                 "Pointwise seems to have succeded with %s\n"
                                 uu____6676);
                          (let uu____6677 = push_goals gs  in
                           bind uu____6677
                             (fun uu____6681  ->
                                add_goals
                                  [(let uu___108_6683 = g  in
                                    {
                                      FStar_Tactics_Types.context =
                                        (uu___108_6683.FStar_Tactics_Types.context);
                                      FStar_Tactics_Types.witness =
                                        (uu___108_6683.FStar_Tactics_Types.witness);
                                      FStar_Tactics_Types.goal_ty = gt';
                                      FStar_Tactics_Types.opts =
                                        (uu___108_6683.FStar_Tactics_Types.opts);
                                      FStar_Tactics_Types.is_guard =
                                        (uu___108_6683.FStar_Tactics_Types.is_guard)
                                    })]))))))
  
let (trefl : Prims.unit tac) =
  bind cur_goal
    (fun g  ->
       let uu____6705 =
         FStar_Syntax_Util.un_squash g.FStar_Tactics_Types.goal_ty  in
       match uu____6705 with
       | FStar_Pervasives_Native.Some t ->
           let uu____6717 = FStar_Syntax_Util.head_and_args' t  in
           (match uu____6717 with
            | (hd1,args) ->
                let uu____6750 =
                  let uu____6763 =
                    let uu____6764 = FStar_Syntax_Util.un_uinst hd1  in
                    uu____6764.FStar_Syntax_Syntax.n  in
                  (uu____6763, args)  in
                (match uu____6750 with
                 | (FStar_Syntax_Syntax.Tm_fvar
                    fv,uu____6778::(l,uu____6780)::(r,uu____6782)::[]) when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.eq2_lid
                     ->
                     let uu____6829 =
                       let uu____6830 =
                         do_unify g.FStar_Tactics_Types.context l r  in
                       Prims.op_Negation uu____6830  in
                     if uu____6829
                     then
                       let uu____6833 = tts g.FStar_Tactics_Types.context l
                          in
                       let uu____6834 = tts g.FStar_Tactics_Types.context r
                          in
                       fail2 "trefl: not a trivial equality (%s vs %s)"
                         uu____6833 uu____6834
                     else solve g FStar_Syntax_Util.exp_unit
                 | (hd2,uu____6837) ->
                     let uu____6854 = tts g.FStar_Tactics_Types.context t  in
                     fail1 "trefl: not an equality (%s)" uu____6854))
       | FStar_Pervasives_Native.None  -> fail "not an irrelevant goal")
  
let (dup : Prims.unit tac) =
  bind cur_goal
    (fun g  ->
       let uu____6864 =
         new_uvar "dup" g.FStar_Tactics_Types.context
           g.FStar_Tactics_Types.goal_ty
          in
       bind uu____6864
         (fun u  ->
            let g' =
              let uu___109_6871 = g  in
              {
                FStar_Tactics_Types.context =
                  (uu___109_6871.FStar_Tactics_Types.context);
                FStar_Tactics_Types.witness = u;
                FStar_Tactics_Types.goal_ty =
                  (uu___109_6871.FStar_Tactics_Types.goal_ty);
                FStar_Tactics_Types.opts =
                  (uu___109_6871.FStar_Tactics_Types.opts);
                FStar_Tactics_Types.is_guard =
                  (uu___109_6871.FStar_Tactics_Types.is_guard)
              }  in
            bind dismiss
              (fun uu____6874  ->
                 let uu____6875 =
                   let uu____6878 =
                     let uu____6879 =
                       FStar_TypeChecker_TcTerm.universe_of
                         g.FStar_Tactics_Types.context
                         g.FStar_Tactics_Types.goal_ty
                        in
                     FStar_Syntax_Util.mk_eq2 uu____6879
                       g.FStar_Tactics_Types.goal_ty u
                       g.FStar_Tactics_Types.witness
                      in
                   add_irrelevant_goal "dup equation"
                     g.FStar_Tactics_Types.context uu____6878
                     g.FStar_Tactics_Types.opts
                    in
                 bind uu____6875
                   (fun uu____6882  ->
                      let uu____6883 = add_goals [g']  in
                      bind uu____6883 (fun uu____6887  -> ret ())))))
  
let (flip : Prims.unit tac) =
  bind get
    (fun ps  ->
       match ps.FStar_Tactics_Types.goals with
       | g1::g2::gs ->
           set
             (let uu___110_6906 = ps  in
              {
                FStar_Tactics_Types.main_context =
                  (uu___110_6906.FStar_Tactics_Types.main_context);
                FStar_Tactics_Types.main_goal =
                  (uu___110_6906.FStar_Tactics_Types.main_goal);
                FStar_Tactics_Types.all_implicits =
                  (uu___110_6906.FStar_Tactics_Types.all_implicits);
                FStar_Tactics_Types.goals = (g2 :: g1 :: gs);
                FStar_Tactics_Types.smt_goals =
                  (uu___110_6906.FStar_Tactics_Types.smt_goals);
                FStar_Tactics_Types.depth =
                  (uu___110_6906.FStar_Tactics_Types.depth);
                FStar_Tactics_Types.__dump =
                  (uu___110_6906.FStar_Tactics_Types.__dump);
                FStar_Tactics_Types.psc =
                  (uu___110_6906.FStar_Tactics_Types.psc);
                FStar_Tactics_Types.entry_range =
                  (uu___110_6906.FStar_Tactics_Types.entry_range)
              })
       | uu____6907 -> fail "flip: less than 2 goals")
  
let (later : Prims.unit tac) =
  bind get
    (fun ps  ->
       match ps.FStar_Tactics_Types.goals with
       | [] -> ret ()
       | g::gs ->
           set
             (let uu___111_6924 = ps  in
              {
                FStar_Tactics_Types.main_context =
                  (uu___111_6924.FStar_Tactics_Types.main_context);
                FStar_Tactics_Types.main_goal =
                  (uu___111_6924.FStar_Tactics_Types.main_goal);
                FStar_Tactics_Types.all_implicits =
                  (uu___111_6924.FStar_Tactics_Types.all_implicits);
                FStar_Tactics_Types.goals = (FStar_List.append gs [g]);
                FStar_Tactics_Types.smt_goals =
                  (uu___111_6924.FStar_Tactics_Types.smt_goals);
                FStar_Tactics_Types.depth =
                  (uu___111_6924.FStar_Tactics_Types.depth);
                FStar_Tactics_Types.__dump =
                  (uu___111_6924.FStar_Tactics_Types.__dump);
                FStar_Tactics_Types.psc =
                  (uu___111_6924.FStar_Tactics_Types.psc);
                FStar_Tactics_Types.entry_range =
                  (uu___111_6924.FStar_Tactics_Types.entry_range)
              }))
  
let (qed : Prims.unit tac) =
  bind get
    (fun ps  ->
       match ps.FStar_Tactics_Types.goals with
       | [] -> ret ()
       | uu____6933 -> fail "Not done!")
  
let (cases :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 tac)
  =
  fun t  ->
    let uu____6951 =
      bind cur_goal
        (fun g  ->
           let uu____6965 = __tc g.FStar_Tactics_Types.context t  in
           bind uu____6965
             (fun uu____7001  ->
                match uu____7001 with
                | (t1,typ,guard) ->
                    let uu____7017 = FStar_Syntax_Util.head_and_args typ  in
                    (match uu____7017 with
                     | (hd1,args) ->
                         let uu____7060 =
                           let uu____7073 =
                             let uu____7074 = FStar_Syntax_Util.un_uinst hd1
                                in
                             uu____7074.FStar_Syntax_Syntax.n  in
                           (uu____7073, args)  in
                         (match uu____7060 with
                          | (FStar_Syntax_Syntax.Tm_fvar
                             fv,(p,uu____7093)::(q,uu____7095)::[]) when
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
                                let uu___112_7133 = g  in
                                let uu____7134 =
                                  FStar_TypeChecker_Env.push_bv
                                    g.FStar_Tactics_Types.context v_p
                                   in
                                {
                                  FStar_Tactics_Types.context = uu____7134;
                                  FStar_Tactics_Types.witness =
                                    (uu___112_7133.FStar_Tactics_Types.witness);
                                  FStar_Tactics_Types.goal_ty =
                                    (uu___112_7133.FStar_Tactics_Types.goal_ty);
                                  FStar_Tactics_Types.opts =
                                    (uu___112_7133.FStar_Tactics_Types.opts);
                                  FStar_Tactics_Types.is_guard =
                                    (uu___112_7133.FStar_Tactics_Types.is_guard)
                                }  in
                              let g2 =
                                let uu___113_7136 = g  in
                                let uu____7137 =
                                  FStar_TypeChecker_Env.push_bv
                                    g.FStar_Tactics_Types.context v_q
                                   in
                                {
                                  FStar_Tactics_Types.context = uu____7137;
                                  FStar_Tactics_Types.witness =
                                    (uu___113_7136.FStar_Tactics_Types.witness);
                                  FStar_Tactics_Types.goal_ty =
                                    (uu___113_7136.FStar_Tactics_Types.goal_ty);
                                  FStar_Tactics_Types.opts =
                                    (uu___113_7136.FStar_Tactics_Types.opts);
                                  FStar_Tactics_Types.is_guard =
                                    (uu___113_7136.FStar_Tactics_Types.is_guard)
                                }  in
                              bind dismiss
                                (fun uu____7144  ->
                                   let uu____7145 = add_goals [g1; g2]  in
                                   bind uu____7145
                                     (fun uu____7154  ->
                                        let uu____7155 =
                                          let uu____7160 =
                                            FStar_Syntax_Syntax.bv_to_name
                                              v_p
                                             in
                                          let uu____7161 =
                                            FStar_Syntax_Syntax.bv_to_name
                                              v_q
                                             in
                                          (uu____7160, uu____7161)  in
                                        ret uu____7155))
                          | uu____7166 ->
                              let uu____7179 =
                                tts g.FStar_Tactics_Types.context typ  in
                              fail1 "Not a disjunction: %s" uu____7179))))
       in
    FStar_All.pipe_left (wrap_err "cases") uu____6951
  
let (set_options : Prims.string -> Prims.unit tac) =
  fun s  ->
    bind cur_goal
      (fun g  ->
         FStar_Options.push ();
         (let uu____7217 = FStar_Util.smap_copy g.FStar_Tactics_Types.opts
             in
          FStar_Options.set uu____7217);
         (let res = FStar_Options.set_options FStar_Options.Set s  in
          let opts' = FStar_Options.peek ()  in
          FStar_Options.pop ();
          (match res with
           | FStar_Getopt.Success  ->
               let g' =
                 let uu___114_7224 = g  in
                 {
                   FStar_Tactics_Types.context =
                     (uu___114_7224.FStar_Tactics_Types.context);
                   FStar_Tactics_Types.witness =
                     (uu___114_7224.FStar_Tactics_Types.witness);
                   FStar_Tactics_Types.goal_ty =
                     (uu___114_7224.FStar_Tactics_Types.goal_ty);
                   FStar_Tactics_Types.opts = opts';
                   FStar_Tactics_Types.is_guard =
                     (uu___114_7224.FStar_Tactics_Types.is_guard)
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
      let uu____7268 =
        bind cur_goal
          (fun goal  ->
             let env =
               FStar_TypeChecker_Env.set_expected_typ
                 goal.FStar_Tactics_Types.context ty
                in
             let uu____7276 = __tc env tm  in
             bind uu____7276
               (fun uu____7296  ->
                  match uu____7296 with
                  | (tm1,typ,guard) ->
                      (FStar_TypeChecker_Rel.force_trivial_guard env guard;
                       ret tm1)))
         in
      FStar_All.pipe_left (wrap_err "unquote") uu____7268
  
let (uvar_env :
  env ->
    FStar_Syntax_Syntax.typ FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.term tac)
  =
  fun env  ->
    fun ty  ->
      let uu____7327 =
        match ty with
        | FStar_Pervasives_Native.Some ty1 -> ret ty1
        | FStar_Pervasives_Native.None  ->
            let uu____7333 =
              let uu____7334 = FStar_Syntax_Util.type_u ()  in
              FStar_All.pipe_left FStar_Pervasives_Native.fst uu____7334  in
            new_uvar "uvar_env.2" env uu____7333
         in
      bind uu____7327
        (fun typ  ->
           let uu____7346 = new_uvar "uvar_env" env typ  in
           bind uu____7346 (fun t  -> ret t))
  
let (unshelve : FStar_Syntax_Syntax.term -> Prims.unit tac) =
  fun t  ->
    let uu____7358 =
      bind cur_goal
        (fun goal  ->
           let uu____7364 = __tc goal.FStar_Tactics_Types.context t  in
           bind uu____7364
             (fun uu____7384  ->
                match uu____7384 with
                | (t1,typ,guard) ->
                    let uu____7396 =
                      must_trivial goal.FStar_Tactics_Types.context guard  in
                    bind uu____7396
                      (fun uu____7401  ->
                         let uu____7402 =
                           let uu____7405 =
                             let uu___115_7406 = goal  in
                             let uu____7407 =
                               bnorm goal.FStar_Tactics_Types.context t1  in
                             let uu____7408 =
                               bnorm goal.FStar_Tactics_Types.context typ  in
                             {
                               FStar_Tactics_Types.context =
                                 (uu___115_7406.FStar_Tactics_Types.context);
                               FStar_Tactics_Types.witness = uu____7407;
                               FStar_Tactics_Types.goal_ty = uu____7408;
                               FStar_Tactics_Types.opts =
                                 (uu___115_7406.FStar_Tactics_Types.opts);
                               FStar_Tactics_Types.is_guard = false
                             }  in
                           [uu____7405]  in
                         add_goals uu____7402)))
       in
    FStar_All.pipe_left (wrap_err "unshelve") uu____7358
  
let (unify :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool tac) =
  fun t1  ->
    fun t2  ->
      bind get
        (fun ps  ->
           let uu____7426 =
             do_unify ps.FStar_Tactics_Types.main_context t1 t2  in
           ret uu____7426)
  
let (launch_process :
  Prims.string -> Prims.string -> Prims.string -> Prims.string tac) =
  fun prog  ->
    fun args  ->
      fun input  ->
        bind idtac
          (fun uu____7443  ->
             let uu____7444 = FStar_Options.unsafe_tactic_exec ()  in
             if uu____7444
             then
               let s =
                 FStar_Util.launch_process true "tactic_launch" prog args
                   input (fun uu____7450  -> fun uu____7451  -> false)
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
        (fun uu____7465  ->
           let uu____7466 =
             FStar_Syntax_Syntax.gen_bv nm FStar_Pervasives_Native.None t  in
           ret uu____7466)
  
let (goal_of_goal_ty :
  env ->
    FStar_Syntax_Syntax.typ ->
      (FStar_Tactics_Types.goal,FStar_TypeChecker_Env.guard_t)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun typ  ->
      let uu____7481 =
        FStar_TypeChecker_Util.new_implicit_var "proofstate_of_goal_ty"
          typ.FStar_Syntax_Syntax.pos env typ
         in
      match uu____7481 with
      | (u,uu____7499,g_u) ->
          let g =
            let uu____7514 = FStar_Options.peek ()  in
            {
              FStar_Tactics_Types.context = env;
              FStar_Tactics_Types.witness = u;
              FStar_Tactics_Types.goal_ty = typ;
              FStar_Tactics_Types.opts = uu____7514;
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
      let uu____7525 = goal_of_goal_ty env typ  in
      match uu____7525 with
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
  