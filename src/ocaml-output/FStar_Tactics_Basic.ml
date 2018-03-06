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
                let uu____420 =
                  FStar_List.map goal_to_json ps.FStar_Tactics_Types.goals
                   in
                FStar_Util.JsonList uu____420  in
              ("goals", uu____419)  in
            let uu____423 =
              let uu____430 =
                let uu____435 =
                  let uu____436 =
                    FStar_List.map goal_to_json
                      ps.FStar_Tactics_Types.smt_goals
                     in
                  FStar_Util.JsonList uu____436  in
                ("smt-goals", uu____435)  in
              [uu____430]  in
            uu____414 :: uu____423  in
          ("label", (FStar_Util.JsonStr msg)) :: uu____407  in
        FStar_Util.JsonAssoc uu____400
  
let (dump_proofstate :
  FStar_Tactics_Types.proofstate -> Prims.string -> Prims.unit) =
  fun ps  ->
    fun msg  ->
      FStar_Options.with_saved_options
        (fun uu____463  ->
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
         (let uu____484 = FStar_Tactics_Types.subst_proof_state subst1 ps  in
          dump_cur uu____484 msg);
         FStar_Tactics_Result.Success ((), ps))
  
let (print_proof_state : Prims.string -> Prims.unit tac) =
  fun msg  ->
    mk_tac
      (fun ps  ->
         let psc = ps.FStar_Tactics_Types.psc  in
         let subst1 = FStar_TypeChecker_Normalize.psc_subst psc  in
         (let uu____500 = FStar_Tactics_Types.subst_proof_state subst1 ps  in
          dump_proofstate uu____500 msg);
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
      let uu____535 = FStar_ST.op_Bang tac_verb_dbg  in
      match uu____535 with
      | FStar_Pervasives_Native.None  ->
          ((let uu____562 =
              let uu____565 =
                FStar_TypeChecker_Env.debug
                  ps.FStar_Tactics_Types.main_context
                  (FStar_Options.Other "TacVerbose")
                 in
              FStar_Pervasives_Native.Some uu____565  in
            FStar_ST.op_Colon_Equals tac_verb_dbg uu____562);
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
         (let uu____634 =
            FStar_TypeChecker_Env.debug ps.FStar_Tactics_Types.main_context
              (FStar_Options.Other "TacFail")
             in
          if uu____634
          then dump_proofstate ps (Prims.strcat "TACTING FAILING: " msg)
          else ());
         FStar_Tactics_Result.Failed (msg, ps))
  
let fail1 : 'Auu____639 . Prims.string -> Prims.string -> 'Auu____639 tac =
  fun msg  ->
    fun x  -> let uu____650 = FStar_Util.format1 msg x  in fail uu____650
  
let fail2 :
  'Auu____655 .
    Prims.string -> Prims.string -> Prims.string -> 'Auu____655 tac
  =
  fun msg  ->
    fun x  ->
      fun y  -> let uu____670 = FStar_Util.format2 msg x y  in fail uu____670
  
let fail3 :
  'Auu____676 .
    Prims.string ->
      Prims.string -> Prims.string -> Prims.string -> 'Auu____676 tac
  =
  fun msg  ->
    fun x  ->
      fun y  ->
        fun z  ->
          let uu____695 = FStar_Util.format3 msg x y z  in fail uu____695
  
let fail4 :
  'Auu____702 .
    Prims.string ->
      Prims.string ->
        Prims.string -> Prims.string -> Prims.string -> 'Auu____702 tac
  =
  fun msg  ->
    fun x  ->
      fun y  ->
        fun z  ->
          fun w  ->
            let uu____725 = FStar_Util.format4 msg x y z w  in fail uu____725
  
let trytac' : 'a . 'a tac -> (Prims.string,'a) FStar_Util.either tac =
  fun t  ->
    mk_tac
      (fun ps  ->
         let tx = FStar_Syntax_Unionfind.new_transaction ()  in
         let uu____755 = run t ps  in
         match uu____755 with
         | FStar_Tactics_Result.Success (a,q) ->
             (FStar_Syntax_Unionfind.commit tx;
              FStar_Tactics_Result.Success ((FStar_Util.Inr a), q))
         | FStar_Tactics_Result.Failed (m,uu____776) ->
             (FStar_Syntax_Unionfind.rollback tx;
              FStar_Tactics_Result.Success ((FStar_Util.Inl m), ps)))
  
let trytac : 'a . 'a tac -> 'a FStar_Pervasives_Native.option tac =
  fun t  ->
    let uu____801 = trytac' t  in
    bind uu____801
      (fun r  ->
         match r with
         | FStar_Util.Inr v1 -> ret (FStar_Pervasives_Native.Some v1)
         | FStar_Util.Inl uu____828 -> ret FStar_Pervasives_Native.None)
  
let wrap_err : 'a . Prims.string -> 'a tac -> 'a tac =
  fun pref  ->
    fun t  ->
      mk_tac
        (fun ps  ->
           let uu____854 = run t ps  in
           match uu____854 with
           | FStar_Tactics_Result.Success (a,q) ->
               FStar_Tactics_Result.Success (a, q)
           | FStar_Tactics_Result.Failed (msg,q) ->
               FStar_Tactics_Result.Failed
                 ((Prims.strcat pref (Prims.strcat ": " msg)), q))
  
let (set : FStar_Tactics_Types.proofstate -> Prims.unit tac) =
  fun p  -> mk_tac (fun uu____871  -> FStar_Tactics_Result.Success ((), p)) 
let (do_unify :
  env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let debug_on uu____884 =
          let uu____885 =
            FStar_Options.set_options FStar_Options.Set
              "--debug_level Rel --debug_level RelCheck"
             in
          ()  in
        let debug_off uu____889 =
          let uu____890 = FStar_Options.set_options FStar_Options.Reset ""
             in
          ()  in
        (let uu____892 =
           FStar_TypeChecker_Env.debug env (FStar_Options.Other "1346")  in
         if uu____892
         then
           (debug_on ();
            (let uu____894 = FStar_Syntax_Print.term_to_string t1  in
             let uu____895 = FStar_Syntax_Print.term_to_string t2  in
             FStar_Util.print2 "%%%%%%%%do_unify %s =? %s\n" uu____894
               uu____895))
         else ());
        (try
           let res = FStar_TypeChecker_Rel.teq_nosmt env t1 t2  in
           debug_off (); res
         with | uu____907 -> (debug_off (); false))
  
let (trysolve :
  FStar_Tactics_Types.goal -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun goal  ->
    fun solution  ->
      do_unify goal.FStar_Tactics_Types.context solution
        goal.FStar_Tactics_Types.witness
  
let (dismiss : Prims.unit tac) =
  bind get
    (fun p  ->
       let uu____920 =
         let uu___61_921 = p  in
         let uu____922 = FStar_List.tl p.FStar_Tactics_Types.goals  in
         {
           FStar_Tactics_Types.main_context =
             (uu___61_921.FStar_Tactics_Types.main_context);
           FStar_Tactics_Types.main_goal =
             (uu___61_921.FStar_Tactics_Types.main_goal);
           FStar_Tactics_Types.all_implicits =
             (uu___61_921.FStar_Tactics_Types.all_implicits);
           FStar_Tactics_Types.goals = uu____922;
           FStar_Tactics_Types.smt_goals =
             (uu___61_921.FStar_Tactics_Types.smt_goals);
           FStar_Tactics_Types.depth =
             (uu___61_921.FStar_Tactics_Types.depth);
           FStar_Tactics_Types.__dump =
             (uu___61_921.FStar_Tactics_Types.__dump);
           FStar_Tactics_Types.psc = (uu___61_921.FStar_Tactics_Types.psc);
           FStar_Tactics_Types.entry_range =
             (uu___61_921.FStar_Tactics_Types.entry_range)
         }  in
       set uu____920)
  
let (solve :
  FStar_Tactics_Types.goal -> FStar_Syntax_Syntax.term -> Prims.unit tac) =
  fun goal  ->
    fun solution  ->
      let uu____935 = trysolve goal solution  in
      if uu____935
      then dismiss
      else
        (let uu____939 =
           let uu____940 = tts goal.FStar_Tactics_Types.context solution  in
           let uu____941 =
             tts goal.FStar_Tactics_Types.context
               goal.FStar_Tactics_Types.witness
              in
           let uu____942 =
             tts goal.FStar_Tactics_Types.context
               goal.FStar_Tactics_Types.goal_ty
              in
           FStar_Util.format3 "%s does not solve %s : %s" uu____940 uu____941
             uu____942
            in
         fail uu____939)
  
let (dismiss_all : Prims.unit tac) =
  bind get
    (fun p  ->
       set
         (let uu___62_949 = p  in
          {
            FStar_Tactics_Types.main_context =
              (uu___62_949.FStar_Tactics_Types.main_context);
            FStar_Tactics_Types.main_goal =
              (uu___62_949.FStar_Tactics_Types.main_goal);
            FStar_Tactics_Types.all_implicits =
              (uu___62_949.FStar_Tactics_Types.all_implicits);
            FStar_Tactics_Types.goals = [];
            FStar_Tactics_Types.smt_goals =
              (uu___62_949.FStar_Tactics_Types.smt_goals);
            FStar_Tactics_Types.depth =
              (uu___62_949.FStar_Tactics_Types.depth);
            FStar_Tactics_Types.__dump =
              (uu___62_949.FStar_Tactics_Types.__dump);
            FStar_Tactics_Types.psc = (uu___62_949.FStar_Tactics_Types.psc);
            FStar_Tactics_Types.entry_range =
              (uu___62_949.FStar_Tactics_Types.entry_range)
          }))
  
let (nwarn : Prims.int FStar_ST.ref) =
  FStar_Util.mk_ref (Prims.parse_int "0") 
let (check_valid_goal : FStar_Tactics_Types.goal -> Prims.unit) =
  fun g  ->
    let uu____966 = FStar_Options.defensive ()  in
    if uu____966
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
        let uu____978 = FStar_TypeChecker_Env.pop_bv e  in
        match uu____978 with
        | FStar_Pervasives_Native.None  -> b3
        | FStar_Pervasives_Native.Some (bv,e1) ->
            let b4 =
              b3 &&
                (FStar_TypeChecker_Env.closed e1 bv.FStar_Syntax_Syntax.sort)
               in
            aux b4 e1
         in
      let uu____996 =
        (let uu____999 = aux b2 env  in Prims.op_Negation uu____999) &&
          (let uu____1001 = FStar_ST.op_Bang nwarn  in
           uu____1001 < (Prims.parse_int "5"))
         in
      (if uu____996
       then
         ((let uu____1022 =
             let uu____1027 =
               let uu____1028 = goal_to_string g  in
               FStar_Util.format1
                 "The following goal is ill-formed. Keeping calm and carrying on...\n<%s>\n\n"
                 uu____1028
                in
             (FStar_Errors.Warning_IllFormedGoal, uu____1027)  in
           FStar_Errors.log_issue
             (g.FStar_Tactics_Types.goal_ty).FStar_Syntax_Syntax.pos
             uu____1022);
          (let uu____1029 =
             let uu____1030 = FStar_ST.op_Bang nwarn  in
             uu____1030 + (Prims.parse_int "1")  in
           FStar_ST.op_Colon_Equals nwarn uu____1029))
       else ())
    else ()
  
let (add_goals : FStar_Tactics_Types.goal Prims.list -> Prims.unit tac) =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___63_1088 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___63_1088.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___63_1088.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___63_1088.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (FStar_List.append gs p.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___63_1088.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___63_1088.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___63_1088.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___63_1088.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___63_1088.FStar_Tactics_Types.entry_range)
            }))
  
let (add_smt_goals : FStar_Tactics_Types.goal Prims.list -> Prims.unit tac) =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___64_1106 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___64_1106.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___64_1106.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___64_1106.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___64_1106.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (FStar_List.append gs p.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___64_1106.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___64_1106.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___64_1106.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___64_1106.FStar_Tactics_Types.entry_range)
            }))
  
let (push_goals : FStar_Tactics_Types.goal Prims.list -> Prims.unit tac) =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___65_1124 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___65_1124.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___65_1124.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___65_1124.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (FStar_List.append p.FStar_Tactics_Types.goals gs);
              FStar_Tactics_Types.smt_goals =
                (uu___65_1124.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___65_1124.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___65_1124.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___65_1124.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___65_1124.FStar_Tactics_Types.entry_range)
            }))
  
let (push_smt_goals : FStar_Tactics_Types.goal Prims.list -> Prims.unit tac)
  =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___66_1142 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___66_1142.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___66_1142.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___66_1142.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___66_1142.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (FStar_List.append p.FStar_Tactics_Types.smt_goals gs);
              FStar_Tactics_Types.depth =
                (uu___66_1142.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___66_1142.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___66_1142.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___66_1142.FStar_Tactics_Types.entry_range)
            }))
  
let (replace_cur : FStar_Tactics_Types.goal -> Prims.unit tac) =
  fun g  -> bind dismiss (fun uu____1151  -> add_goals [g]) 
let (add_implicits : implicits -> Prims.unit tac) =
  fun i  ->
    bind get
      (fun p  ->
         set
           (let uu___67_1163 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___67_1163.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___67_1163.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (FStar_List.append i p.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___67_1163.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___67_1163.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___67_1163.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___67_1163.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___67_1163.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___67_1163.FStar_Tactics_Types.entry_range)
            }))
  
let (new_uvar :
  Prims.string ->
    env -> FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.term tac)
  =
  fun reason  ->
    fun env  ->
      fun typ  ->
        let uu____1189 =
          FStar_TypeChecker_Util.new_implicit_var reason
            typ.FStar_Syntax_Syntax.pos env typ
           in
        match uu____1189 with
        | (u,uu____1205,g_u) ->
            let uu____1219 =
              add_implicits g_u.FStar_TypeChecker_Env.implicits  in
            bind uu____1219 (fun uu____1223  -> ret u)
  
let (is_true : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____1227 = FStar_Syntax_Util.un_squash t  in
    match uu____1227 with
    | FStar_Pervasives_Native.Some t' ->
        let uu____1237 =
          let uu____1238 = FStar_Syntax_Subst.compress t'  in
          uu____1238.FStar_Syntax_Syntax.n  in
        (match uu____1237 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.true_lid
         | uu____1242 -> false)
    | uu____1243 -> false
  
let (is_false : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____1251 = FStar_Syntax_Util.un_squash t  in
    match uu____1251 with
    | FStar_Pervasives_Native.Some t' ->
        let uu____1261 =
          let uu____1262 = FStar_Syntax_Subst.compress t'  in
          uu____1262.FStar_Syntax_Syntax.n  in
        (match uu____1261 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.false_lid
         | uu____1266 -> false)
    | uu____1267 -> false
  
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
            let uu____1307 = env.FStar_TypeChecker_Env.universe_of env phi
               in
            FStar_Syntax_Util.mk_squash uu____1307 phi  in
          let uu____1308 = new_uvar reason env typ  in
          bind uu____1308
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
             let uu____1364 =
               (ps.FStar_Tactics_Types.main_context).FStar_TypeChecker_Env.type_of
                 e t
                in
             ret uu____1364
           with
           | ex ->
               let uu____1391 = tts e t  in
               let uu____1392 =
                 let uu____1393 = FStar_TypeChecker_Env.all_binders e  in
                 FStar_All.pipe_right uu____1393
                   (FStar_Syntax_Print.binders_to_string ", ")
                  in
               fail2 "Cannot type %s in context (%s)" uu____1391 uu____1392)
  
let (must_trivial : env -> FStar_TypeChecker_Env.guard_t -> Prims.unit tac) =
  fun e  ->
    fun g  ->
      try
        let uu____1417 =
          let uu____1418 =
            let uu____1419 = FStar_TypeChecker_Rel.discharge_guard_no_smt e g
               in
            FStar_All.pipe_left FStar_TypeChecker_Rel.is_trivial uu____1419
             in
          Prims.op_Negation uu____1418  in
        if uu____1417 then fail "got non-trivial guard" else ret ()
      with | uu____1428 -> fail "got non-trivial guard"
  
let (tc : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.typ tac) =
  fun t  ->
    let uu____1436 =
      bind cur_goal
        (fun goal  ->
           let uu____1442 = __tc goal.FStar_Tactics_Types.context t  in
           bind uu____1442
             (fun uu____1462  ->
                match uu____1462 with
                | (t1,typ,guard) ->
                    let uu____1474 =
                      must_trivial goal.FStar_Tactics_Types.context guard  in
                    bind uu____1474 (fun uu____1478  -> ret typ)))
       in
    FStar_All.pipe_left (wrap_err "tc") uu____1436
  
let (add_irrelevant_goal :
  Prims.string ->
    env ->
      FStar_Syntax_Syntax.typ -> FStar_Options.optionstate -> Prims.unit tac)
  =
  fun reason  ->
    fun env  ->
      fun phi  ->
        fun opts  ->
          let uu____1499 = mk_irrelevant_goal reason env phi opts  in
          bind uu____1499 (fun goal  -> add_goals [goal])
  
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
       let uu____1521 =
         istrivial goal.FStar_Tactics_Types.context
           goal.FStar_Tactics_Types.goal_ty
          in
       if uu____1521
       then solve goal FStar_Syntax_Util.exp_unit
       else
         (let uu____1525 =
            tts goal.FStar_Tactics_Types.context
              goal.FStar_Tactics_Types.goal_ty
             in
          fail1 "Not a trivial goal: %s" uu____1525))
  
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
          let uu____1542 =
            let uu____1543 = FStar_TypeChecker_Rel.simplify_guard e g  in
            uu____1543.FStar_TypeChecker_Env.guard_f  in
          match uu____1542 with
          | FStar_TypeChecker_Common.Trivial  -> ret ()
          | FStar_TypeChecker_Common.NonTrivial f ->
              let uu____1547 = istrivial e f  in
              if uu____1547
              then ret ()
              else
                (let uu____1551 = mk_irrelevant_goal reason e f opts  in
                 bind uu____1551
                   (fun goal  ->
                      let goal1 =
                        let uu___72_1558 = goal  in
                        {
                          FStar_Tactics_Types.context =
                            (uu___72_1558.FStar_Tactics_Types.context);
                          FStar_Tactics_Types.witness =
                            (uu___72_1558.FStar_Tactics_Types.witness);
                          FStar_Tactics_Types.goal_ty =
                            (uu___72_1558.FStar_Tactics_Types.goal_ty);
                          FStar_Tactics_Types.opts =
                            (uu___72_1558.FStar_Tactics_Types.opts);
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
          let uu____1579 =
            let uu____1580 = FStar_TypeChecker_Rel.simplify_guard e g  in
            uu____1580.FStar_TypeChecker_Env.guard_f  in
          match uu____1579 with
          | FStar_TypeChecker_Common.Trivial  ->
              ret FStar_Pervasives_Native.None
          | FStar_TypeChecker_Common.NonTrivial f ->
              let uu____1588 = istrivial e f  in
              if uu____1588
              then ret FStar_Pervasives_Native.None
              else
                (let uu____1596 = mk_irrelevant_goal reason e f opts  in
                 bind uu____1596
                   (fun goal  ->
                      ret
                        (FStar_Pervasives_Native.Some
                           (let uu___73_1606 = goal  in
                            {
                              FStar_Tactics_Types.context =
                                (uu___73_1606.FStar_Tactics_Types.context);
                              FStar_Tactics_Types.witness =
                                (uu___73_1606.FStar_Tactics_Types.witness);
                              FStar_Tactics_Types.goal_ty =
                                (uu___73_1606.FStar_Tactics_Types.goal_ty);
                              FStar_Tactics_Types.opts =
                                (uu___73_1606.FStar_Tactics_Types.opts);
                              FStar_Tactics_Types.is_guard = true
                            }))))
  
let (smt : Prims.unit tac) =
  bind cur_goal
    (fun g  ->
       let uu____1614 = is_irrelevant g  in
       if uu____1614
       then bind dismiss (fun uu____1618  -> add_smt_goals [g])
       else
         (let uu____1620 =
            tts g.FStar_Tactics_Types.context g.FStar_Tactics_Types.goal_ty
             in
          fail1 "goal is not irrelevant: cannot dispatch to smt (%s)"
            uu____1620))
  
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
             let uu____1661 =
               try
                 let uu____1695 =
                   let uu____1704 = FStar_BigInt.to_int_fs n1  in
                   FStar_List.splitAt uu____1704 p.FStar_Tactics_Types.goals
                    in
                 ret uu____1695
               with | uu____1726 -> fail "divide: not enough goals"  in
             bind uu____1661
               (fun uu____1753  ->
                  match uu____1753 with
                  | (lgs,rgs) ->
                      let lp =
                        let uu___74_1779 = p  in
                        {
                          FStar_Tactics_Types.main_context =
                            (uu___74_1779.FStar_Tactics_Types.main_context);
                          FStar_Tactics_Types.main_goal =
                            (uu___74_1779.FStar_Tactics_Types.main_goal);
                          FStar_Tactics_Types.all_implicits =
                            (uu___74_1779.FStar_Tactics_Types.all_implicits);
                          FStar_Tactics_Types.goals = lgs;
                          FStar_Tactics_Types.smt_goals = [];
                          FStar_Tactics_Types.depth =
                            (uu___74_1779.FStar_Tactics_Types.depth);
                          FStar_Tactics_Types.__dump =
                            (uu___74_1779.FStar_Tactics_Types.__dump);
                          FStar_Tactics_Types.psc =
                            (uu___74_1779.FStar_Tactics_Types.psc);
                          FStar_Tactics_Types.entry_range =
                            (uu___74_1779.FStar_Tactics_Types.entry_range)
                        }  in
                      let rp =
                        let uu___75_1781 = p  in
                        {
                          FStar_Tactics_Types.main_context =
                            (uu___75_1781.FStar_Tactics_Types.main_context);
                          FStar_Tactics_Types.main_goal =
                            (uu___75_1781.FStar_Tactics_Types.main_goal);
                          FStar_Tactics_Types.all_implicits =
                            (uu___75_1781.FStar_Tactics_Types.all_implicits);
                          FStar_Tactics_Types.goals = rgs;
                          FStar_Tactics_Types.smt_goals = [];
                          FStar_Tactics_Types.depth =
                            (uu___75_1781.FStar_Tactics_Types.depth);
                          FStar_Tactics_Types.__dump =
                            (uu___75_1781.FStar_Tactics_Types.__dump);
                          FStar_Tactics_Types.psc =
                            (uu___75_1781.FStar_Tactics_Types.psc);
                          FStar_Tactics_Types.entry_range =
                            (uu___75_1781.FStar_Tactics_Types.entry_range)
                        }  in
                      let uu____1782 = set lp  in
                      bind uu____1782
                        (fun uu____1790  ->
                           bind l
                             (fun a  ->
                                bind get
                                  (fun lp'  ->
                                     let uu____1804 = set rp  in
                                     bind uu____1804
                                       (fun uu____1812  ->
                                          bind r
                                            (fun b  ->
                                               bind get
                                                 (fun rp'  ->
                                                    let p' =
                                                      let uu___76_1828 = p
                                                         in
                                                      {
                                                        FStar_Tactics_Types.main_context
                                                          =
                                                          (uu___76_1828.FStar_Tactics_Types.main_context);
                                                        FStar_Tactics_Types.main_goal
                                                          =
                                                          (uu___76_1828.FStar_Tactics_Types.main_goal);
                                                        FStar_Tactics_Types.all_implicits
                                                          =
                                                          (uu___76_1828.FStar_Tactics_Types.all_implicits);
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
                                                          (uu___76_1828.FStar_Tactics_Types.depth);
                                                        FStar_Tactics_Types.__dump
                                                          =
                                                          (uu___76_1828.FStar_Tactics_Types.__dump);
                                                        FStar_Tactics_Types.psc
                                                          =
                                                          (uu___76_1828.FStar_Tactics_Types.psc);
                                                        FStar_Tactics_Types.entry_range
                                                          =
                                                          (uu___76_1828.FStar_Tactics_Types.entry_range)
                                                      }  in
                                                    let uu____1829 = set p'
                                                       in
                                                    bind uu____1829
                                                      (fun uu____1837  ->
                                                         ret (a, b))))))))))
  
let focus : 'a . 'a tac -> 'a tac =
  fun f  ->
    let uu____1855 = divide FStar_BigInt.one f idtac  in
    bind uu____1855
      (fun uu____1868  -> match uu____1868 with | (a,()) -> ret a)
  
let rec map : 'a . 'a tac -> 'a Prims.list tac =
  fun tau  ->
    bind get
      (fun p  ->
         match p.FStar_Tactics_Types.goals with
         | [] -> ret []
         | uu____1902::uu____1903 ->
             let uu____1906 =
               let uu____1915 = map tau  in
               divide FStar_BigInt.one tau uu____1915  in
             bind uu____1906
               (fun uu____1933  ->
                  match uu____1933 with | (h,t) -> ret (h :: t)))
  
let (seq : Prims.unit tac -> Prims.unit tac -> Prims.unit tac) =
  fun t1  ->
    fun t2  ->
      let uu____1970 =
        bind t1
          (fun uu____1975  ->
             let uu____1976 = map t2  in
             bind uu____1976 (fun uu____1984  -> ret ()))
         in
      focus uu____1970
  
let (intro : FStar_Syntax_Syntax.binder tac) =
  let uu____1991 =
    bind cur_goal
      (fun goal  ->
         let uu____2000 =
           FStar_Syntax_Util.arrow_one goal.FStar_Tactics_Types.goal_ty  in
         match uu____2000 with
         | FStar_Pervasives_Native.Some (b,c) ->
             let uu____2015 =
               let uu____2016 = FStar_Syntax_Util.is_total_comp c  in
               Prims.op_Negation uu____2016  in
             if uu____2015
             then fail "Codomain is effectful"
             else
               (let env' =
                  FStar_TypeChecker_Env.push_binders
                    goal.FStar_Tactics_Types.context [b]
                   in
                let typ' = comp_to_typ c  in
                let uu____2022 = new_uvar "intro" env' typ'  in
                bind uu____2022
                  (fun u  ->
                     let uu____2029 =
                       let uu____2030 =
                         FStar_Syntax_Util.abs [b] u
                           FStar_Pervasives_Native.None
                          in
                       trysolve goal uu____2030  in
                     if uu____2029
                     then
                       let uu____2033 =
                         let uu____2036 =
                           let uu___79_2037 = goal  in
                           let uu____2038 = bnorm env' u  in
                           let uu____2039 = bnorm env' typ'  in
                           {
                             FStar_Tactics_Types.context = env';
                             FStar_Tactics_Types.witness = uu____2038;
                             FStar_Tactics_Types.goal_ty = uu____2039;
                             FStar_Tactics_Types.opts =
                               (uu___79_2037.FStar_Tactics_Types.opts);
                             FStar_Tactics_Types.is_guard =
                               (uu___79_2037.FStar_Tactics_Types.is_guard)
                           }  in
                         replace_cur uu____2036  in
                       bind uu____2033 (fun uu____2041  -> ret b)
                     else fail "unification failed"))
         | FStar_Pervasives_Native.None  ->
             let uu____2047 =
               tts goal.FStar_Tactics_Types.context
                 goal.FStar_Tactics_Types.goal_ty
                in
             fail1 "goal is not an arrow (%s)" uu____2047)
     in
  FStar_All.pipe_left (wrap_err "intro") uu____1991 
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
       (let uu____2078 =
          FStar_Syntax_Util.arrow_one goal.FStar_Tactics_Types.goal_ty  in
        match uu____2078 with
        | FStar_Pervasives_Native.Some (b,c) ->
            let uu____2097 =
              let uu____2098 = FStar_Syntax_Util.is_total_comp c  in
              Prims.op_Negation uu____2098  in
            if uu____2097
            then fail "Codomain is effectful"
            else
              (let bv =
                 FStar_Syntax_Syntax.gen_bv "__recf"
                   FStar_Pervasives_Native.None
                   goal.FStar_Tactics_Types.goal_ty
                  in
               let bs =
                 let uu____2114 = FStar_Syntax_Syntax.mk_binder bv  in
                 [uu____2114; b]  in
               let env' =
                 FStar_TypeChecker_Env.push_binders
                   goal.FStar_Tactics_Types.context bs
                  in
               let uu____2116 =
                 let uu____2119 = comp_to_typ c  in
                 new_uvar "intro_rec" env' uu____2119  in
               bind uu____2116
                 (fun u  ->
                    let lb =
                      let uu____2135 =
                        FStar_Syntax_Util.abs [b] u
                          FStar_Pervasives_Native.None
                         in
                      FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl bv) []
                        goal.FStar_Tactics_Types.goal_ty
                        FStar_Parser_Const.effect_Tot_lid uu____2135 []
                       in
                    let body = FStar_Syntax_Syntax.bv_to_name bv  in
                    let uu____2141 =
                      FStar_Syntax_Subst.close_let_rec [lb] body  in
                    match uu____2141 with
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
                          let uu____2178 =
                            let uu____2181 =
                              let uu___80_2182 = goal  in
                              let uu____2183 = bnorm env' u  in
                              let uu____2184 =
                                let uu____2185 = comp_to_typ c  in
                                bnorm env' uu____2185  in
                              {
                                FStar_Tactics_Types.context = env';
                                FStar_Tactics_Types.witness = uu____2183;
                                FStar_Tactics_Types.goal_ty = uu____2184;
                                FStar_Tactics_Types.opts =
                                  (uu___80_2182.FStar_Tactics_Types.opts);
                                FStar_Tactics_Types.is_guard =
                                  (uu___80_2182.FStar_Tactics_Types.is_guard)
                              }  in
                            replace_cur uu____2181  in
                          bind uu____2178
                            (fun uu____2192  ->
                               let uu____2193 =
                                 let uu____2198 =
                                   FStar_Syntax_Syntax.mk_binder bv  in
                                 (uu____2198, b)  in
                               ret uu____2193)
                        else fail "intro_rec: unification failed"))
        | FStar_Pervasives_Native.None  ->
            let uu____2212 =
              tts goal.FStar_Tactics_Types.context
                goal.FStar_Tactics_Types.goal_ty
               in
            fail1 "intro_rec: goal is not an arrow (%s)" uu____2212))
  
let (norm : FStar_Syntax_Embeddings.norm_step Prims.list -> Prims.unit tac) =
  fun s  ->
    bind cur_goal
      (fun goal  ->
         mlog
           (fun uu____2232  ->
              let uu____2233 =
                FStar_Syntax_Print.term_to_string
                  goal.FStar_Tactics_Types.witness
                 in
              FStar_Util.print1 "norm: witness = %s\n" uu____2233)
           (fun uu____2238  ->
              let steps =
                let uu____2242 = FStar_TypeChecker_Normalize.tr_norm_steps s
                   in
                FStar_List.append
                  [FStar_TypeChecker_Normalize.Reify;
                  FStar_TypeChecker_Normalize.UnfoldTac] uu____2242
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
                (let uu___81_2249 = goal  in
                 {
                   FStar_Tactics_Types.context =
                     (uu___81_2249.FStar_Tactics_Types.context);
                   FStar_Tactics_Types.witness = w;
                   FStar_Tactics_Types.goal_ty = t;
                   FStar_Tactics_Types.opts =
                     (uu___81_2249.FStar_Tactics_Types.opts);
                   FStar_Tactics_Types.is_guard =
                     (uu___81_2249.FStar_Tactics_Types.is_guard)
                 })))
  
let (norm_term_env :
  env ->
    FStar_Syntax_Embeddings.norm_step Prims.list ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac)
  =
  fun e  ->
    fun s  ->
      fun t  ->
        let uu____2267 =
          mlog
            (fun uu____2272  ->
               let uu____2273 = FStar_Syntax_Print.term_to_string t  in
               FStar_Util.print1 "norm_term: tm = %s\n" uu____2273)
            (fun uu____2275  ->
               bind get
                 (fun ps  ->
                    mlog
                      (fun uu____2280  ->
                         let uu____2281 =
                           tts ps.FStar_Tactics_Types.main_context t  in
                         FStar_Util.print1 "norm_term_env: t = %s\n"
                           uu____2281)
                      (fun uu____2284  ->
                         let uu____2285 = __tc e t  in
                         bind uu____2285
                           (fun uu____2307  ->
                              match uu____2307 with
                              | (t1,uu____2317,guard) ->
                                  (FStar_TypeChecker_Rel.force_trivial_guard
                                     e guard;
                                   (let steps =
                                      let uu____2323 =
                                        FStar_TypeChecker_Normalize.tr_norm_steps
                                          s
                                         in
                                      FStar_List.append
                                        [FStar_TypeChecker_Normalize.Reify;
                                        FStar_TypeChecker_Normalize.UnfoldTac]
                                        uu____2323
                                       in
                                    let t2 =
                                      normalize steps
                                        ps.FStar_Tactics_Types.main_context
                                        t1
                                       in
                                    ret t2))))))
           in
        FStar_All.pipe_left (wrap_err "norm_term") uu____2267
  
let (refine_intro : Prims.unit tac) =
  let uu____2335 =
    bind cur_goal
      (fun g  ->
         let uu____2342 =
           FStar_TypeChecker_Rel.base_and_refinement
             g.FStar_Tactics_Types.context g.FStar_Tactics_Types.goal_ty
            in
         match uu____2342 with
         | (uu____2355,FStar_Pervasives_Native.None ) ->
             fail "not a refinement"
         | (t,FStar_Pervasives_Native.Some (bv,phi)) ->
             let g1 =
               let uu___82_2380 = g  in
               {
                 FStar_Tactics_Types.context =
                   (uu___82_2380.FStar_Tactics_Types.context);
                 FStar_Tactics_Types.witness =
                   (uu___82_2380.FStar_Tactics_Types.witness);
                 FStar_Tactics_Types.goal_ty = t;
                 FStar_Tactics_Types.opts =
                   (uu___82_2380.FStar_Tactics_Types.opts);
                 FStar_Tactics_Types.is_guard =
                   (uu___82_2380.FStar_Tactics_Types.is_guard)
               }  in
             let uu____2381 =
               let uu____2386 =
                 let uu____2391 =
                   let uu____2392 = FStar_Syntax_Syntax.mk_binder bv  in
                   [uu____2392]  in
                 FStar_Syntax_Subst.open_term uu____2391 phi  in
               match uu____2386 with
               | (bvs,phi1) ->
                   let uu____2399 =
                     let uu____2400 = FStar_List.hd bvs  in
                     FStar_Pervasives_Native.fst uu____2400  in
                   (uu____2399, phi1)
                in
             (match uu____2381 with
              | (bv1,phi1) ->
                  let uu____2413 =
                    let uu____2416 =
                      FStar_Syntax_Subst.subst
                        [FStar_Syntax_Syntax.NT
                           (bv1, (g.FStar_Tactics_Types.witness))] phi1
                       in
                    mk_irrelevant_goal "refine_intro refinement"
                      g.FStar_Tactics_Types.context uu____2416
                      g.FStar_Tactics_Types.opts
                     in
                  bind uu____2413
                    (fun g2  ->
                       bind dismiss (fun uu____2420  -> add_goals [g1; g2]))))
     in
  FStar_All.pipe_left (wrap_err "refine_intro") uu____2335 
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
             let uu____2444 = __tc env t  in
             bind uu____2444
               (fun uu____2464  ->
                  match uu____2464 with
                  | (t1,typ,guard) ->
                      let uu____2476 =
                        if force_guard
                        then
                          must_trivial goal.FStar_Tactics_Types.context guard
                        else
                          add_goal_from_guard "__exact typing"
                            goal.FStar_Tactics_Types.context guard
                            goal.FStar_Tactics_Types.opts
                         in
                      bind uu____2476
                        (fun uu____2483  ->
                           mlog
                             (fun uu____2487  ->
                                let uu____2488 =
                                  tts goal.FStar_Tactics_Types.context typ
                                   in
                                let uu____2489 =
                                  tts goal.FStar_Tactics_Types.context
                                    goal.FStar_Tactics_Types.goal_ty
                                   in
                                FStar_Util.print2
                                  "exact: unifying %s and %s\n" uu____2488
                                  uu____2489)
                             (fun uu____2492  ->
                                let uu____2493 =
                                  do_unify goal.FStar_Tactics_Types.context
                                    typ goal.FStar_Tactics_Types.goal_ty
                                   in
                                if uu____2493
                                then solve goal t1
                                else
                                  (let uu____2497 =
                                     tts goal.FStar_Tactics_Types.context t1
                                      in
                                   let uu____2498 =
                                     tts goal.FStar_Tactics_Types.context typ
                                      in
                                   let uu____2499 =
                                     tts goal.FStar_Tactics_Types.context
                                       goal.FStar_Tactics_Types.goal_ty
                                      in
                                   let uu____2500 =
                                     tts goal.FStar_Tactics_Types.context
                                       goal.FStar_Tactics_Types.witness
                                      in
                                   fail4
                                     "%s : %s does not exactly solve the goal %s (witness = %s)"
                                     uu____2497 uu____2498 uu____2499
                                     uu____2500)))))
  
let (t_exact :
  Prims.bool -> Prims.bool -> FStar_Syntax_Syntax.term -> Prims.unit tac) =
  fun set_expected_typ1  ->
    fun force_guard  ->
      fun tm  ->
        let uu____2514 =
          mlog
            (fun uu____2519  ->
               let uu____2520 = FStar_Syntax_Print.term_to_string tm  in
               FStar_Util.print1 "t_exact: tm = %s\n" uu____2520)
            (fun uu____2523  ->
               let uu____2524 =
                 let uu____2531 =
                   __exact_now set_expected_typ1 force_guard tm  in
                 trytac' uu____2531  in
               bind uu____2524
                 (fun uu___56_2540  ->
                    match uu___56_2540 with
                    | FStar_Util.Inr r -> ret ()
                    | FStar_Util.Inl e ->
                        let uu____2549 =
                          let uu____2556 =
                            let uu____2559 =
                              norm [FStar_Syntax_Embeddings.Delta]  in
                            bind uu____2559
                              (fun uu____2563  ->
                                 bind refine_intro
                                   (fun uu____2565  ->
                                      __exact_now set_expected_typ1
                                        force_guard tm))
                             in
                          trytac' uu____2556  in
                        bind uu____2549
                          (fun uu___55_2572  ->
                             match uu___55_2572 with
                             | FStar_Util.Inr r -> ret ()
                             | FStar_Util.Inl uu____2580 -> fail e)))
           in
        FStar_All.pipe_left (wrap_err "exact") uu____2514
  
let (uvar_free_in_goal :
  FStar_Syntax_Syntax.uvar -> FStar_Tactics_Types.goal -> Prims.bool) =
  fun u  ->
    fun g  ->
      if g.FStar_Tactics_Types.is_guard
      then false
      else
        (let free_uvars =
           let uu____2595 =
             let uu____2602 =
               FStar_Syntax_Free.uvars g.FStar_Tactics_Types.goal_ty  in
             FStar_Util.set_elements uu____2602  in
           FStar_List.map FStar_Pervasives_Native.fst uu____2595  in
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
          let uu____2662 = f x  in
          bind uu____2662
            (fun y  ->
               let uu____2670 = mapM f xs  in
               bind uu____2670 (fun ys  -> ret (y :: ys)))
  
exception NoUnif 
let (uu___is_NoUnif : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with | NoUnif  -> true | uu____2688 -> false
  
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
               (fun uu____2706  ->
                  let uu____2707 = FStar_Syntax_Print.term_to_string tm  in
                  FStar_Util.print1 ">>> Calling __exact(%s)\n" uu____2707)
               (fun uu____2710  ->
                  let uu____2711 =
                    let uu____2716 = t_exact false true tm  in
                    trytac uu____2716  in
                  bind uu____2711
                    (fun uu___57_2723  ->
                       match uu___57_2723 with
                       | FStar_Pervasives_Native.Some r -> ret ()
                       | FStar_Pervasives_Native.None  ->
                           mlog
                             (fun uu____2731  ->
                                let uu____2732 =
                                  FStar_Syntax_Print.term_to_string typ  in
                                FStar_Util.print1 ">>> typ = %s\n" uu____2732)
                             (fun uu____2735  ->
                                let uu____2736 =
                                  FStar_Syntax_Util.arrow_one typ  in
                                match uu____2736 with
                                | FStar_Pervasives_Native.None  ->
                                    FStar_Exn.raise NoUnif
                                | FStar_Pervasives_Native.Some ((bv,aq),c) ->
                                    mlog
                                      (fun uu____2768  ->
                                         let uu____2769 =
                                           FStar_Syntax_Print.binder_to_string
                                             (bv, aq)
                                            in
                                         FStar_Util.print1
                                           "__apply: pushing binder %s\n"
                                           uu____2769)
                                      (fun uu____2772  ->
                                         let uu____2773 =
                                           let uu____2774 =
                                             FStar_Syntax_Util.is_total_comp
                                               c
                                              in
                                           Prims.op_Negation uu____2774  in
                                         if uu____2773
                                         then
                                           fail "apply: not total codomain"
                                         else
                                           (let uu____2778 =
                                              new_uvar "apply"
                                                goal.FStar_Tactics_Types.context
                                                bv.FStar_Syntax_Syntax.sort
                                               in
                                            bind uu____2778
                                              (fun u  ->
                                                 let tm' =
                                                   FStar_Syntax_Syntax.mk_Tm_app
                                                     tm [(u, aq)]
                                                     FStar_Pervasives_Native.None
                                                     tm.FStar_Syntax_Syntax.pos
                                                    in
                                                 let typ' =
                                                   let uu____2798 =
                                                     comp_to_typ c  in
                                                   FStar_All.pipe_left
                                                     (FStar_Syntax_Subst.subst
                                                        [FStar_Syntax_Syntax.NT
                                                           (bv, u)])
                                                     uu____2798
                                                    in
                                                 let uu____2799 =
                                                   __apply uopt tm' typ'  in
                                                 bind uu____2799
                                                   (fun uu____2807  ->
                                                      let u1 =
                                                        bnorm
                                                          goal.FStar_Tactics_Types.context
                                                          u
                                                         in
                                                      let uu____2809 =
                                                        let uu____2810 =
                                                          let uu____2813 =
                                                            let uu____2814 =
                                                              FStar_Syntax_Util.head_and_args
                                                                u1
                                                               in
                                                            FStar_Pervasives_Native.fst
                                                              uu____2814
                                                             in
                                                          FStar_Syntax_Subst.compress
                                                            uu____2813
                                                           in
                                                        uu____2810.FStar_Syntax_Syntax.n
                                                         in
                                                      match uu____2809 with
                                                      | FStar_Syntax_Syntax.Tm_uvar
                                                          (uvar,uu____2842)
                                                          ->
                                                          bind get
                                                            (fun ps  ->
                                                               let uu____2870
                                                                 =
                                                                 uopt &&
                                                                   (uvar_free
                                                                    uvar ps)
                                                                  in
                                                               if uu____2870
                                                               then ret ()
                                                               else
                                                                 (let uu____2874
                                                                    =
                                                                    let uu____2877
                                                                    =
                                                                    let uu___83_2878
                                                                    = goal
                                                                     in
                                                                    let uu____2879
                                                                    =
                                                                    bnorm
                                                                    goal.FStar_Tactics_Types.context
                                                                    u1  in
                                                                    let uu____2880
                                                                    =
                                                                    bnorm
                                                                    goal.FStar_Tactics_Types.context
                                                                    bv.FStar_Syntax_Syntax.sort
                                                                     in
                                                                    {
                                                                    FStar_Tactics_Types.context
                                                                    =
                                                                    (uu___83_2878.FStar_Tactics_Types.context);
                                                                    FStar_Tactics_Types.witness
                                                                    =
                                                                    uu____2879;
                                                                    FStar_Tactics_Types.goal_ty
                                                                    =
                                                                    uu____2880;
                                                                    FStar_Tactics_Types.opts
                                                                    =
                                                                    (uu___83_2878.FStar_Tactics_Types.opts);
                                                                    FStar_Tactics_Types.is_guard
                                                                    = false
                                                                    }  in
                                                                    [uu____2877]
                                                                     in
                                                                  add_goals
                                                                    uu____2874))
                                                      | t -> ret ()))))))))
  
let try_unif : 'a . 'a tac -> 'a tac -> 'a tac =
  fun t  ->
    fun t'  -> mk_tac (fun ps  -> try run t ps with | NoUnif  -> run t' ps)
  
let (apply : Prims.bool -> FStar_Syntax_Syntax.term -> Prims.unit tac) =
  fun uopt  ->
    fun tm  ->
      let uu____2926 =
        mlog
          (fun uu____2931  ->
             let uu____2932 = FStar_Syntax_Print.term_to_string tm  in
             FStar_Util.print1 "apply: tm = %s\n" uu____2932)
          (fun uu____2934  ->
             bind cur_goal
               (fun goal  ->
                  let uu____2938 = __tc goal.FStar_Tactics_Types.context tm
                     in
                  bind uu____2938
                    (fun uu____2959  ->
                       match uu____2959 with
                       | (tm1,typ,guard) ->
                           let uu____2971 =
                             let uu____2974 =
                               let uu____2977 = __apply uopt tm1 typ  in
                               bind uu____2977
                                 (fun uu____2981  ->
                                    add_goal_from_guard "apply guard"
                                      goal.FStar_Tactics_Types.context guard
                                      goal.FStar_Tactics_Types.opts)
                                in
                             focus uu____2974  in
                           let uu____2982 =
                             let uu____2985 =
                               tts goal.FStar_Tactics_Types.context tm1  in
                             let uu____2986 =
                               tts goal.FStar_Tactics_Types.context typ  in
                             let uu____2987 =
                               tts goal.FStar_Tactics_Types.context
                                 goal.FStar_Tactics_Types.goal_ty
                                in
                             fail3
                               "Cannot instantiate %s (of type %s) to match goal (%s)"
                               uu____2985 uu____2986 uu____2987
                              in
                           try_unif uu____2971 uu____2982)))
         in
      FStar_All.pipe_left (wrap_err "apply") uu____2926
  
let (apply_lemma : FStar_Syntax_Syntax.term -> Prims.unit tac) =
  fun tm  ->
    let uu____2999 =
      let uu____3002 =
        mlog
          (fun uu____3007  ->
             let uu____3008 = FStar_Syntax_Print.term_to_string tm  in
             FStar_Util.print1 "apply_lemma: tm = %s\n" uu____3008)
          (fun uu____3011  ->
             let is_unit_t t =
               let uu____3016 =
                 let uu____3017 = FStar_Syntax_Subst.compress t  in
                 uu____3017.FStar_Syntax_Syntax.n  in
               match uu____3016 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.unit_lid
                   -> true
               | uu____3021 -> false  in
             bind cur_goal
               (fun goal  ->
                  let uu____3025 = __tc goal.FStar_Tactics_Types.context tm
                     in
                  bind uu____3025
                    (fun uu____3047  ->
                       match uu____3047 with
                       | (tm1,t,guard) ->
                           let uu____3059 =
                             FStar_Syntax_Util.arrow_formals_comp t  in
                           (match uu____3059 with
                            | (bs,comp) ->
                                if
                                  Prims.op_Negation
                                    (FStar_Syntax_Util.is_lemma_comp comp)
                                then fail "not a lemma"
                                else
                                  (let uu____3089 =
                                     FStar_List.fold_left
                                       (fun uu____3135  ->
                                          fun uu____3136  ->
                                            match (uu____3135, uu____3136)
                                            with
                                            | ((uvs,guard1,subst1),(b,aq)) ->
                                                let b_t =
                                                  FStar_Syntax_Subst.subst
                                                    subst1
                                                    b.FStar_Syntax_Syntax.sort
                                                   in
                                                let uu____3239 =
                                                  is_unit_t b_t  in
                                                if uu____3239
                                                then
                                                  (((FStar_Syntax_Util.exp_unit,
                                                      aq) :: uvs), guard1,
                                                    ((FStar_Syntax_Syntax.NT
                                                        (b,
                                                          FStar_Syntax_Util.exp_unit))
                                                    :: subst1))
                                                else
                                                  (let uu____3277 =
                                                     FStar_TypeChecker_Util.new_implicit_var
                                                       "apply_lemma"
                                                       (goal.FStar_Tactics_Types.goal_ty).FStar_Syntax_Syntax.pos
                                                       goal.FStar_Tactics_Types.context
                                                       b_t
                                                      in
                                                   match uu____3277 with
                                                   | (u,uu____3307,g_u) ->
                                                       let uu____3321 =
                                                         FStar_TypeChecker_Rel.conj_guard
                                                           guard1 g_u
                                                          in
                                                       (((u, aq) :: uvs),
                                                         uu____3321,
                                                         ((FStar_Syntax_Syntax.NT
                                                             (b, u)) ::
                                                         subst1))))
                                       ([], guard, []) bs
                                      in
                                   match uu____3089 with
                                   | (uvs,implicits,subst1) ->
                                       let uvs1 = FStar_List.rev uvs  in
                                       let comp1 =
                                         FStar_Syntax_Subst.subst_comp subst1
                                           comp
                                          in
                                       let uu____3391 =
                                         let uu____3400 =
                                           let uu____3409 =
                                             FStar_Syntax_Util.comp_to_comp_typ
                                               comp1
                                              in
                                           uu____3409.FStar_Syntax_Syntax.effect_args
                                            in
                                         match uu____3400 with
                                         | pre::post::uu____3420 ->
                                             ((FStar_Pervasives_Native.fst
                                                 pre),
                                               (FStar_Pervasives_Native.fst
                                                  post))
                                         | uu____3461 ->
                                             failwith
                                               "apply_lemma: impossible: not a lemma"
                                          in
                                       (match uu____3391 with
                                        | (pre,post) ->
                                            let post1 =
                                              let uu____3493 =
                                                let uu____3502 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    FStar_Syntax_Util.exp_unit
                                                   in
                                                [uu____3502]  in
                                              FStar_Syntax_Util.mk_app post
                                                uu____3493
                                               in
                                            let uu____3503 =
                                              let uu____3504 =
                                                let uu____3505 =
                                                  FStar_Syntax_Util.mk_squash
                                                    FStar_Syntax_Syntax.U_zero
                                                    post1
                                                   in
                                                do_unify
                                                  goal.FStar_Tactics_Types.context
                                                  uu____3505
                                                  goal.FStar_Tactics_Types.goal_ty
                                                 in
                                              Prims.op_Negation uu____3504
                                               in
                                            if uu____3503
                                            then
                                              let uu____3508 =
                                                tts
                                                  goal.FStar_Tactics_Types.context
                                                  tm1
                                                 in
                                              let uu____3509 =
                                                let uu____3510 =
                                                  FStar_Syntax_Util.mk_squash
                                                    FStar_Syntax_Syntax.U_zero
                                                    post1
                                                   in
                                                tts
                                                  goal.FStar_Tactics_Types.context
                                                  uu____3510
                                                 in
                                              let uu____3511 =
                                                tts
                                                  goal.FStar_Tactics_Types.context
                                                  goal.FStar_Tactics_Types.goal_ty
                                                 in
                                              fail3
                                                "Cannot instantiate lemma %s (with postcondition: %s) to match goal (%s)"
                                                uu____3508 uu____3509
                                                uu____3511
                                            else
                                              (let uu____3513 =
                                                 add_implicits
                                                   implicits.FStar_TypeChecker_Env.implicits
                                                  in
                                               bind uu____3513
                                                 (fun uu____3518  ->
                                                    let uu____3519 =
                                                      solve goal
                                                        FStar_Syntax_Util.exp_unit
                                                       in
                                                    bind uu____3519
                                                      (fun uu____3527  ->
                                                         let is_free_uvar uv
                                                           t1 =
                                                           let free_uvars =
                                                             let uu____3538 =
                                                               let uu____3545
                                                                 =
                                                                 FStar_Syntax_Free.uvars
                                                                   t1
                                                                  in
                                                               FStar_Util.set_elements
                                                                 uu____3545
                                                                in
                                                             FStar_List.map
                                                               FStar_Pervasives_Native.fst
                                                               uu____3538
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
                                                           let uu____3586 =
                                                             FStar_Syntax_Util.head_and_args
                                                               t1
                                                              in
                                                           match uu____3586
                                                           with
                                                           | (hd1,uu____3602)
                                                               ->
                                                               (match 
                                                                  hd1.FStar_Syntax_Syntax.n
                                                                with
                                                                | FStar_Syntax_Syntax.Tm_uvar
                                                                    (uv,uu____3624)
                                                                    ->
                                                                    appears
                                                                    uv goals
                                                                | uu____3649
                                                                    -> false)
                                                            in
                                                         let uu____3650 =
                                                           FStar_All.pipe_right
                                                             implicits.FStar_TypeChecker_Env.implicits
                                                             (mapM
                                                                (fun
                                                                   uu____3722
                                                                    ->
                                                                   match uu____3722
                                                                   with
                                                                   | 
                                                                   (_msg,env,_uvar,term,typ,uu____3750)
                                                                    ->
                                                                    let uu____3751
                                                                    =
                                                                    FStar_Syntax_Util.head_and_args
                                                                    term  in
                                                                    (match uu____3751
                                                                    with
                                                                    | 
                                                                    (hd1,uu____3777)
                                                                    ->
                                                                    let uu____3798
                                                                    =
                                                                    let uu____3799
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    hd1  in
                                                                    uu____3799.FStar_Syntax_Syntax.n
                                                                     in
                                                                    (match uu____3798
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Tm_uvar
                                                                    uu____3812
                                                                    ->
                                                                    let uu____3829
                                                                    =
                                                                    let uu____3838
                                                                    =
                                                                    let uu____3841
                                                                    =
                                                                    let uu___86_3842
                                                                    = goal
                                                                     in
                                                                    let uu____3843
                                                                    =
                                                                    bnorm
                                                                    goal.FStar_Tactics_Types.context
                                                                    term  in
                                                                    let uu____3844
                                                                    =
                                                                    bnorm
                                                                    goal.FStar_Tactics_Types.context
                                                                    typ  in
                                                                    {
                                                                    FStar_Tactics_Types.context
                                                                    =
                                                                    (uu___86_3842.FStar_Tactics_Types.context);
                                                                    FStar_Tactics_Types.witness
                                                                    =
                                                                    uu____3843;
                                                                    FStar_Tactics_Types.goal_ty
                                                                    =
                                                                    uu____3844;
                                                                    FStar_Tactics_Types.opts
                                                                    =
                                                                    (uu___86_3842.FStar_Tactics_Types.opts);
                                                                    FStar_Tactics_Types.is_guard
                                                                    =
                                                                    (uu___86_3842.FStar_Tactics_Types.is_guard)
                                                                    }  in
                                                                    [uu____3841]
                                                                     in
                                                                    (uu____3838,
                                                                    [])  in
                                                                    ret
                                                                    uu____3829
                                                                    | 
                                                                    uu____3857
                                                                    ->
                                                                    let g_typ
                                                                    =
                                                                    let uu____3859
                                                                    =
                                                                    FStar_Options.__temp_fast_implicits
                                                                    ()  in
                                                                    if
                                                                    uu____3859
                                                                    then
                                                                    FStar_TypeChecker_TcTerm.check_type_of_well_typed_term
                                                                    false env
                                                                    term typ
                                                                    else
                                                                    (let term1
                                                                    =
                                                                    bnorm env
                                                                    term  in
                                                                    let uu____3862
                                                                    =
                                                                    let uu____3869
                                                                    =
                                                                    FStar_TypeChecker_Env.set_expected_typ
                                                                    env typ
                                                                     in
                                                                    env.FStar_TypeChecker_Env.type_of
                                                                    uu____3869
                                                                    term1  in
                                                                    match uu____3862
                                                                    with
                                                                    | 
                                                                    (uu____3870,uu____3871,g_typ)
                                                                    -> g_typ)
                                                                     in
                                                                    let uu____3873
                                                                    =
                                                                    goal_from_guard
                                                                    "apply_lemma solved arg"
                                                                    goal.FStar_Tactics_Types.context
                                                                    g_typ
                                                                    goal.FStar_Tactics_Types.opts
                                                                     in
                                                                    bind
                                                                    uu____3873
                                                                    (fun
                                                                    uu___58_3889
                                                                     ->
                                                                    match uu___58_3889
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
                                                         bind uu____3650
                                                           (fun goals_  ->
                                                              let sub_goals =
                                                                let uu____3957
                                                                  =
                                                                  FStar_List.map
                                                                    FStar_Pervasives_Native.fst
                                                                    goals_
                                                                   in
                                                                FStar_List.flatten
                                                                  uu____3957
                                                                 in
                                                              let smt_goals =
                                                                let uu____3979
                                                                  =
                                                                  FStar_List.map
                                                                    FStar_Pervasives_Native.snd
                                                                    goals_
                                                                   in
                                                                FStar_List.flatten
                                                                  uu____3979
                                                                 in
                                                              let rec filter'
                                                                a f xs =
                                                                match xs with
                                                                | [] -> []
                                                                | x::xs1 ->
                                                                    let uu____4034
                                                                    = f x xs1
                                                                     in
                                                                    if
                                                                    uu____4034
                                                                    then
                                                                    let uu____4037
                                                                    =
                                                                    filter'
                                                                    () f xs1
                                                                     in x ::
                                                                    uu____4037
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
                                                                    let uu____4051
                                                                    =
                                                                    checkone
                                                                    g.FStar_Tactics_Types.witness
                                                                    goals  in
                                                                    Prims.op_Negation
                                                                    uu____4051))
                                                                    a431 a432)
                                                                    (Obj.magic
                                                                    sub_goals))
                                                                 in
                                                              let uu____4052
                                                                =
                                                                add_goal_from_guard
                                                                  "apply_lemma guard"
                                                                  goal.FStar_Tactics_Types.context
                                                                  guard
                                                                  goal.FStar_Tactics_Types.opts
                                                                 in
                                                              bind uu____4052
                                                                (fun
                                                                   uu____4057
                                                                    ->
                                                                   let uu____4058
                                                                    =
                                                                    let uu____4061
                                                                    =
                                                                    let uu____4062
                                                                    =
                                                                    let uu____4063
                                                                    =
                                                                    FStar_Syntax_Util.mk_squash
                                                                    FStar_Syntax_Syntax.U_zero
                                                                    pre  in
                                                                    istrivial
                                                                    goal.FStar_Tactics_Types.context
                                                                    uu____4063
                                                                     in
                                                                    Prims.op_Negation
                                                                    uu____4062
                                                                     in
                                                                    if
                                                                    uu____4061
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
                                                                    uu____4058
                                                                    (fun
                                                                    uu____4069
                                                                     ->
                                                                    let uu____4070
                                                                    =
                                                                    add_smt_goals
                                                                    smt_goals
                                                                     in
                                                                    bind
                                                                    uu____4070
                                                                    (fun
                                                                    uu____4074
                                                                     ->
                                                                    add_goals
                                                                    sub_goals1)))))))))))))
         in
      focus uu____3002  in
    FStar_All.pipe_left (wrap_err "apply_lemma") uu____2999
  
let (destruct_eq' :
  FStar_Syntax_Syntax.typ ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun typ  ->
    let uu____4094 = FStar_Syntax_Util.destruct_typ_as_formula typ  in
    match uu____4094 with
    | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn
        (l,uu____4104::(e1,uu____4106)::(e2,uu____4108)::[])) when
        FStar_Ident.lid_equals l FStar_Parser_Const.eq2_lid ->
        FStar_Pervasives_Native.Some (e1, e2)
    | uu____4167 -> FStar_Pervasives_Native.None
  
let (destruct_eq :
  FStar_Syntax_Syntax.typ ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun typ  ->
    let uu____4189 = destruct_eq' typ  in
    match uu____4189 with
    | FStar_Pervasives_Native.Some t -> FStar_Pervasives_Native.Some t
    | FStar_Pervasives_Native.None  ->
        let uu____4219 = FStar_Syntax_Util.un_squash typ  in
        (match uu____4219 with
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
        let uu____4275 = FStar_TypeChecker_Env.pop_bv e1  in
        match uu____4275 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (bv',e') ->
            if FStar_Syntax_Syntax.bv_eq bvar bv'
            then FStar_Pervasives_Native.Some (e', [])
            else
              (let uu____4323 = aux e'  in
               FStar_Util.map_opt uu____4323
                 (fun uu____4347  ->
                    match uu____4347 with | (e'',bvs) -> (e'', (bv' :: bvs))))
         in
      let uu____4368 = aux e  in
      FStar_Util.map_opt uu____4368
        (fun uu____4392  ->
           match uu____4392 with | (e',bvs) -> (e', (FStar_List.rev bvs)))
  
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
          let uu____4447 = split_env b1 g.FStar_Tactics_Types.context  in
          FStar_Util.map_opt uu____4447
            (fun uu____4471  ->
               match uu____4471 with
               | (e0,bvs) ->
                   let s1 bv =
                     let uu___87_4488 = bv  in
                     let uu____4489 =
                       FStar_Syntax_Subst.subst s bv.FStar_Syntax_Syntax.sort
                        in
                     {
                       FStar_Syntax_Syntax.ppname =
                         (uu___87_4488.FStar_Syntax_Syntax.ppname);
                       FStar_Syntax_Syntax.index =
                         (uu___87_4488.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort = uu____4489
                     }  in
                   let bvs1 = FStar_List.map s1 bvs  in
                   let c = push_bvs e0 (b2 :: bvs1)  in
                   let w =
                     FStar_Syntax_Subst.subst s g.FStar_Tactics_Types.witness
                      in
                   let t =
                     FStar_Syntax_Subst.subst s g.FStar_Tactics_Types.goal_ty
                      in
                   let uu___88_4498 = g  in
                   {
                     FStar_Tactics_Types.context = c;
                     FStar_Tactics_Types.witness = w;
                     FStar_Tactics_Types.goal_ty = t;
                     FStar_Tactics_Types.opts =
                       (uu___88_4498.FStar_Tactics_Types.opts);
                     FStar_Tactics_Types.is_guard =
                       (uu___88_4498.FStar_Tactics_Types.is_guard)
                   })
  
let (rewrite : FStar_Syntax_Syntax.binder -> Prims.unit tac) =
  fun h  ->
    bind cur_goal
      (fun goal  ->
         let uu____4511 = h  in
         match uu____4511 with
         | (bv,uu____4515) ->
             mlog
               (fun uu____4519  ->
                  let uu____4520 = FStar_Syntax_Print.bv_to_string bv  in
                  let uu____4521 =
                    tts goal.FStar_Tactics_Types.context
                      bv.FStar_Syntax_Syntax.sort
                     in
                  FStar_Util.print2 "+++Rewrite %s : %s\n" uu____4520
                    uu____4521)
               (fun uu____4524  ->
                  let uu____4525 =
                    split_env bv goal.FStar_Tactics_Types.context  in
                  match uu____4525 with
                  | FStar_Pervasives_Native.None  ->
                      fail "rewrite: binder not found in environment"
                  | FStar_Pervasives_Native.Some (e0,bvs) ->
                      let uu____4554 =
                        destruct_eq bv.FStar_Syntax_Syntax.sort  in
                      (match uu____4554 with
                       | FStar_Pervasives_Native.Some (x,e) ->
                           let uu____4569 =
                             let uu____4570 = FStar_Syntax_Subst.compress x
                                in
                             uu____4570.FStar_Syntax_Syntax.n  in
                           (match uu____4569 with
                            | FStar_Syntax_Syntax.Tm_name x1 ->
                                let s = [FStar_Syntax_Syntax.NT (x1, e)]  in
                                let s1 bv1 =
                                  let uu___89_4583 = bv1  in
                                  let uu____4584 =
                                    FStar_Syntax_Subst.subst s
                                      bv1.FStar_Syntax_Syntax.sort
                                     in
                                  {
                                    FStar_Syntax_Syntax.ppname =
                                      (uu___89_4583.FStar_Syntax_Syntax.ppname);
                                    FStar_Syntax_Syntax.index =
                                      (uu___89_4583.FStar_Syntax_Syntax.index);
                                    FStar_Syntax_Syntax.sort = uu____4584
                                  }  in
                                let bvs1 = FStar_List.map s1 bvs  in
                                let uu____4590 =
                                  let uu___90_4591 = goal  in
                                  let uu____4592 = push_bvs e0 (bv :: bvs1)
                                     in
                                  let uu____4593 =
                                    FStar_Syntax_Subst.subst s
                                      goal.FStar_Tactics_Types.witness
                                     in
                                  let uu____4594 =
                                    FStar_Syntax_Subst.subst s
                                      goal.FStar_Tactics_Types.goal_ty
                                     in
                                  {
                                    FStar_Tactics_Types.context = uu____4592;
                                    FStar_Tactics_Types.witness = uu____4593;
                                    FStar_Tactics_Types.goal_ty = uu____4594;
                                    FStar_Tactics_Types.opts =
                                      (uu___90_4591.FStar_Tactics_Types.opts);
                                    FStar_Tactics_Types.is_guard =
                                      (uu___90_4591.FStar_Tactics_Types.is_guard)
                                  }  in
                                replace_cur uu____4590
                            | uu____4595 ->
                                fail
                                  "rewrite: Not an equality hypothesis with a variable on the LHS")
                       | uu____4596 ->
                           fail "rewrite: Not an equality hypothesis")))
  
let (rename_to :
  FStar_Syntax_Syntax.binder -> Prims.string -> Prims.unit tac) =
  fun b  ->
    fun s  ->
      bind cur_goal
        (fun goal  ->
           let uu____4621 = b  in
           match uu____4621 with
           | (bv,uu____4625) ->
               let bv' =
                 FStar_Syntax_Syntax.freshen_bv
                   (let uu___91_4629 = bv  in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (FStar_Ident.mk_ident
                           (s,
                             ((bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange)));
                      FStar_Syntax_Syntax.index =
                        (uu___91_4629.FStar_Syntax_Syntax.index);
                      FStar_Syntax_Syntax.sort =
                        (uu___91_4629.FStar_Syntax_Syntax.sort)
                    })
                  in
               let s1 =
                 let uu____4633 =
                   let uu____4634 =
                     let uu____4641 = FStar_Syntax_Syntax.bv_to_name bv'  in
                     (bv, uu____4641)  in
                   FStar_Syntax_Syntax.NT uu____4634  in
                 [uu____4633]  in
               let uu____4642 = subst_goal bv bv' s1 goal  in
               (match uu____4642 with
                | FStar_Pervasives_Native.None  ->
                    fail "rename_to: binder not found in environment"
                | FStar_Pervasives_Native.Some goal1 -> replace_cur goal1))
  
let (binder_retype : FStar_Syntax_Syntax.binder -> Prims.unit tac) =
  fun b  ->
    bind cur_goal
      (fun goal  ->
         let uu____4661 = b  in
         match uu____4661 with
         | (bv,uu____4665) ->
             let uu____4666 = split_env bv goal.FStar_Tactics_Types.context
                in
             (match uu____4666 with
              | FStar_Pervasives_Native.None  ->
                  fail "binder_retype: binder is not present in environment"
              | FStar_Pervasives_Native.Some (e0,bvs) ->
                  let uu____4695 = FStar_Syntax_Util.type_u ()  in
                  (match uu____4695 with
                   | (ty,u) ->
                       let uu____4704 = new_uvar "binder_retype" e0 ty  in
                       bind uu____4704
                         (fun t'  ->
                            let bv'' =
                              let uu___92_4714 = bv  in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___92_4714.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___92_4714.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = t'
                              }  in
                            let s =
                              let uu____4718 =
                                let uu____4719 =
                                  let uu____4726 =
                                    FStar_Syntax_Syntax.bv_to_name bv''  in
                                  (bv, uu____4726)  in
                                FStar_Syntax_Syntax.NT uu____4719  in
                              [uu____4718]  in
                            let bvs1 =
                              FStar_List.map
                                (fun b1  ->
                                   let uu___93_4734 = b1  in
                                   let uu____4735 =
                                     FStar_Syntax_Subst.subst s
                                       b1.FStar_Syntax_Syntax.sort
                                      in
                                   {
                                     FStar_Syntax_Syntax.ppname =
                                       (uu___93_4734.FStar_Syntax_Syntax.ppname);
                                     FStar_Syntax_Syntax.index =
                                       (uu___93_4734.FStar_Syntax_Syntax.index);
                                     FStar_Syntax_Syntax.sort = uu____4735
                                   }) bvs
                               in
                            let env' = push_bvs e0 (bv'' :: bvs1)  in
                            bind dismiss
                              (fun uu____4741  ->
                                 let uu____4742 =
                                   let uu____4745 =
                                     let uu____4748 =
                                       let uu___94_4749 = goal  in
                                       let uu____4750 =
                                         FStar_Syntax_Subst.subst s
                                           goal.FStar_Tactics_Types.witness
                                          in
                                       let uu____4751 =
                                         FStar_Syntax_Subst.subst s
                                           goal.FStar_Tactics_Types.goal_ty
                                          in
                                       {
                                         FStar_Tactics_Types.context = env';
                                         FStar_Tactics_Types.witness =
                                           uu____4750;
                                         FStar_Tactics_Types.goal_ty =
                                           uu____4751;
                                         FStar_Tactics_Types.opts =
                                           (uu___94_4749.FStar_Tactics_Types.opts);
                                         FStar_Tactics_Types.is_guard =
                                           (uu___94_4749.FStar_Tactics_Types.is_guard)
                                       }  in
                                     [uu____4748]  in
                                   add_goals uu____4745  in
                                 bind uu____4742
                                   (fun uu____4754  ->
                                      let uu____4755 =
                                        FStar_Syntax_Util.mk_eq2
                                          (FStar_Syntax_Syntax.U_succ u) ty
                                          bv.FStar_Syntax_Syntax.sort t'
                                         in
                                      add_irrelevant_goal
                                        "binder_retype equation" e0
                                        uu____4755
                                        goal.FStar_Tactics_Types.opts))))))
  
let (norm_binder_type :
  FStar_Syntax_Embeddings.norm_step Prims.list ->
    FStar_Syntax_Syntax.binder -> Prims.unit tac)
  =
  fun s  ->
    fun b  ->
      bind cur_goal
        (fun goal  ->
           let uu____4776 = b  in
           match uu____4776 with
           | (bv,uu____4780) ->
               let uu____4781 = split_env bv goal.FStar_Tactics_Types.context
                  in
               (match uu____4781 with
                | FStar_Pervasives_Native.None  ->
                    fail
                      "binder_retype: binder is not present in environment"
                | FStar_Pervasives_Native.Some (e0,bvs) ->
                    let steps =
                      let uu____4813 =
                        FStar_TypeChecker_Normalize.tr_norm_steps s  in
                      FStar_List.append
                        [FStar_TypeChecker_Normalize.Reify;
                        FStar_TypeChecker_Normalize.UnfoldTac] uu____4813
                       in
                    let sort' =
                      normalize steps e0 bv.FStar_Syntax_Syntax.sort  in
                    let bv' =
                      let uu___95_4818 = bv  in
                      {
                        FStar_Syntax_Syntax.ppname =
                          (uu___95_4818.FStar_Syntax_Syntax.ppname);
                        FStar_Syntax_Syntax.index =
                          (uu___95_4818.FStar_Syntax_Syntax.index);
                        FStar_Syntax_Syntax.sort = sort'
                      }  in
                    let env' = push_bvs e0 (bv' :: bvs)  in
                    replace_cur
                      (let uu___96_4822 = goal  in
                       {
                         FStar_Tactics_Types.context = env';
                         FStar_Tactics_Types.witness =
                           (uu___96_4822.FStar_Tactics_Types.witness);
                         FStar_Tactics_Types.goal_ty =
                           (uu___96_4822.FStar_Tactics_Types.goal_ty);
                         FStar_Tactics_Types.opts =
                           (uu___96_4822.FStar_Tactics_Types.opts);
                         FStar_Tactics_Types.is_guard =
                           (uu___96_4822.FStar_Tactics_Types.is_guard)
                       })))
  
let (revert : Prims.unit tac) =
  bind cur_goal
    (fun goal  ->
       let uu____4830 =
         FStar_TypeChecker_Env.pop_bv goal.FStar_Tactics_Types.context  in
       match uu____4830 with
       | FStar_Pervasives_Native.None  -> fail "Cannot revert; empty context"
       | FStar_Pervasives_Native.Some (x,env') ->
           let typ' =
             let uu____4852 =
               FStar_Syntax_Syntax.mk_Total goal.FStar_Tactics_Types.goal_ty
                in
             FStar_Syntax_Util.arrow [(x, FStar_Pervasives_Native.None)]
               uu____4852
              in
           let w' =
             FStar_Syntax_Util.abs [(x, FStar_Pervasives_Native.None)]
               goal.FStar_Tactics_Types.witness FStar_Pervasives_Native.None
              in
           replace_cur
             (let uu___97_4886 = goal  in
              {
                FStar_Tactics_Types.context = env';
                FStar_Tactics_Types.witness = w';
                FStar_Tactics_Types.goal_ty = typ';
                FStar_Tactics_Types.opts =
                  (uu___97_4886.FStar_Tactics_Types.opts);
                FStar_Tactics_Types.is_guard =
                  (uu___97_4886.FStar_Tactics_Types.is_guard)
              }))
  
let (free_in :
  FStar_Syntax_Syntax.bv -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun bv  ->
    fun t  ->
      let uu____4893 = FStar_Syntax_Free.names t  in
      FStar_Util.set_mem bv uu____4893
  
let rec (clear : FStar_Syntax_Syntax.binder -> Prims.unit tac) =
  fun b  ->
    let bv = FStar_Pervasives_Native.fst b  in
    bind cur_goal
      (fun goal  ->
         mlog
           (fun uu____4909  ->
              let uu____4910 = FStar_Syntax_Print.binder_to_string b  in
              let uu____4911 =
                let uu____4912 =
                  let uu____4913 =
                    FStar_TypeChecker_Env.all_binders
                      goal.FStar_Tactics_Types.context
                     in
                  FStar_All.pipe_right uu____4913 FStar_List.length  in
                FStar_All.pipe_right uu____4912 FStar_Util.string_of_int  in
              FStar_Util.print2 "Clear of (%s), env has %s binders\n"
                uu____4910 uu____4911)
           (fun uu____4924  ->
              let uu____4925 = split_env bv goal.FStar_Tactics_Types.context
                 in
              match uu____4925 with
              | FStar_Pervasives_Native.None  ->
                  fail "Cannot clear; binder not in environment"
              | FStar_Pervasives_Native.Some (e',bvs) ->
                  let rec check bvs1 =
                    match bvs1 with
                    | [] -> ret ()
                    | bv'::bvs2 ->
                        let uu____4970 =
                          free_in bv bv'.FStar_Syntax_Syntax.sort  in
                        if uu____4970
                        then
                          let uu____4973 =
                            let uu____4974 =
                              FStar_Syntax_Print.bv_to_string bv'  in
                            FStar_Util.format1
                              "Cannot clear; binder present in the type of %s"
                              uu____4974
                             in
                          fail uu____4973
                        else check bvs2
                     in
                  let uu____4976 =
                    free_in bv goal.FStar_Tactics_Types.goal_ty  in
                  if uu____4976
                  then fail "Cannot clear; binder present in goal"
                  else
                    (let uu____4980 = check bvs  in
                     bind uu____4980
                       (fun uu____4986  ->
                          let env' = push_bvs e' bvs  in
                          let uu____4988 =
                            new_uvar "clear.witness" env'
                              goal.FStar_Tactics_Types.goal_ty
                             in
                          bind uu____4988
                            (fun ut  ->
                               let uu____4994 =
                                 do_unify goal.FStar_Tactics_Types.context
                                   goal.FStar_Tactics_Types.witness ut
                                  in
                               if uu____4994
                               then
                                 replace_cur
                                   (let uu___98_4999 = goal  in
                                    {
                                      FStar_Tactics_Types.context = env';
                                      FStar_Tactics_Types.witness = ut;
                                      FStar_Tactics_Types.goal_ty =
                                        (uu___98_4999.FStar_Tactics_Types.goal_ty);
                                      FStar_Tactics_Types.opts =
                                        (uu___98_4999.FStar_Tactics_Types.opts);
                                      FStar_Tactics_Types.is_guard =
                                        (uu___98_4999.FStar_Tactics_Types.is_guard)
                                    })
                               else
                                 fail
                                   "Cannot clear; binder appears in witness")))))
  
let (clear_top : Prims.unit tac) =
  bind cur_goal
    (fun goal  ->
       let uu____5008 =
         FStar_TypeChecker_Env.pop_bv goal.FStar_Tactics_Types.context  in
       match uu____5008 with
       | FStar_Pervasives_Native.None  -> fail "Cannot clear; empty context"
       | FStar_Pervasives_Native.Some (x,uu____5022) ->
           let uu____5027 = FStar_Syntax_Syntax.mk_binder x  in
           clear uu____5027)
  
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
           let uu___99_5043 = g  in
           {
             FStar_Tactics_Types.context = ctx';
             FStar_Tactics_Types.witness =
               (uu___99_5043.FStar_Tactics_Types.witness);
             FStar_Tactics_Types.goal_ty =
               (uu___99_5043.FStar_Tactics_Types.goal_ty);
             FStar_Tactics_Types.opts =
               (uu___99_5043.FStar_Tactics_Types.opts);
             FStar_Tactics_Types.is_guard =
               (uu___99_5043.FStar_Tactics_Types.is_guard)
           }  in
         bind dismiss (fun uu____5045  -> add_goals [g']))
  
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
           let uu___100_5061 = g  in
           {
             FStar_Tactics_Types.context = ctx';
             FStar_Tactics_Types.witness =
               (uu___100_5061.FStar_Tactics_Types.witness);
             FStar_Tactics_Types.goal_ty =
               (uu___100_5061.FStar_Tactics_Types.goal_ty);
             FStar_Tactics_Types.opts =
               (uu___100_5061.FStar_Tactics_Types.opts);
             FStar_Tactics_Types.is_guard =
               (uu___100_5061.FStar_Tactics_Types.is_guard)
           }  in
         bind dismiss (fun uu____5063  -> add_goals [g']))
  
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
            let uu____5095 = FStar_Syntax_Subst.compress t  in
            uu____5095.FStar_Syntax_Syntax.n  in
          let uu____5098 =
            if d = FStar_Tactics_Types.TopDown
            then
              f env
                (let uu___102_5104 = t  in
                 {
                   FStar_Syntax_Syntax.n = tn;
                   FStar_Syntax_Syntax.pos =
                     (uu___102_5104.FStar_Syntax_Syntax.pos);
                   FStar_Syntax_Syntax.vars =
                     (uu___102_5104.FStar_Syntax_Syntax.vars)
                 })
            else ret t  in
          bind uu____5098
            (fun t1  ->
               let tn1 =
                 let uu____5112 =
                   let uu____5113 = FStar_Syntax_Subst.compress t1  in
                   uu____5113.FStar_Syntax_Syntax.n  in
                 match uu____5112 with
                 | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
                     let ff = tac_fold_env d f env  in
                     let uu____5145 = ff hd1  in
                     bind uu____5145
                       (fun hd2  ->
                          let fa uu____5165 =
                            match uu____5165 with
                            | (a,q) ->
                                let uu____5178 = ff a  in
                                bind uu____5178 (fun a1  -> ret (a1, q))
                             in
                          let uu____5191 = mapM fa args  in
                          bind uu____5191
                            (fun args1  ->
                               ret (FStar_Syntax_Syntax.Tm_app (hd2, args1))))
                 | FStar_Syntax_Syntax.Tm_abs (bs,t2,k) ->
                     let uu____5251 = FStar_Syntax_Subst.open_term bs t2  in
                     (match uu____5251 with
                      | (bs1,t') ->
                          let uu____5260 =
                            let uu____5263 =
                              FStar_TypeChecker_Env.push_binders env bs1  in
                            tac_fold_env d f uu____5263 t'  in
                          bind uu____5260
                            (fun t''  ->
                               let uu____5267 =
                                 let uu____5268 =
                                   let uu____5285 =
                                     FStar_Syntax_Subst.close_binders bs1  in
                                   let uu____5286 =
                                     FStar_Syntax_Subst.close bs1 t''  in
                                   (uu____5285, uu____5286, k)  in
                                 FStar_Syntax_Syntax.Tm_abs uu____5268  in
                               ret uu____5267))
                 | FStar_Syntax_Syntax.Tm_arrow (bs,k) -> ret tn
                 | uu____5307 -> ret tn  in
               bind tn1
                 (fun tn2  ->
                    let t' =
                      let uu___101_5314 = t1  in
                      {
                        FStar_Syntax_Syntax.n = tn2;
                        FStar_Syntax_Syntax.pos =
                          (uu___101_5314.FStar_Syntax_Syntax.pos);
                        FStar_Syntax_Syntax.vars =
                          (uu___101_5314.FStar_Syntax_Syntax.vars)
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
            let uu____5343 = FStar_TypeChecker_TcTerm.tc_term env t  in
            match uu____5343 with
            | (t1,lcomp,g) ->
                let uu____5355 =
                  (let uu____5358 =
                     FStar_Syntax_Util.is_pure_or_ghost_lcomp lcomp  in
                   Prims.op_Negation uu____5358) ||
                    (let uu____5360 = FStar_TypeChecker_Rel.is_trivial g  in
                     Prims.op_Negation uu____5360)
                   in
                if uu____5355
                then ret t1
                else
                  (let rewrite_eq =
                     let typ = lcomp.FStar_Syntax_Syntax.res_typ  in
                     let uu____5370 = new_uvar "pointwise_rec" env typ  in
                     bind uu____5370
                       (fun ut  ->
                          log ps
                            (fun uu____5381  ->
                               let uu____5382 =
                                 FStar_Syntax_Print.term_to_string t1  in
                               let uu____5383 =
                                 FStar_Syntax_Print.term_to_string ut  in
                               FStar_Util.print2
                                 "Pointwise_rec: making equality\n\t%s ==\n\t%s\n"
                                 uu____5382 uu____5383);
                          (let uu____5384 =
                             let uu____5387 =
                               let uu____5388 =
                                 FStar_TypeChecker_TcTerm.universe_of env typ
                                  in
                               FStar_Syntax_Util.mk_eq2 uu____5388 typ t1 ut
                                in
                             add_irrelevant_goal "pointwise_rec equation" env
                               uu____5387 opts
                              in
                           bind uu____5384
                             (fun uu____5391  ->
                                let uu____5392 =
                                  bind tau
                                    (fun uu____5398  ->
                                       let ut1 =
                                         FStar_TypeChecker_Normalize.reduce_uvar_solutions
                                           env ut
                                          in
                                       log ps
                                         (fun uu____5404  ->
                                            let uu____5405 =
                                              FStar_Syntax_Print.term_to_string
                                                t1
                                               in
                                            let uu____5406 =
                                              FStar_Syntax_Print.term_to_string
                                                ut1
                                               in
                                            FStar_Util.print2
                                              "Pointwise_rec: succeeded rewriting\n\t%s to\n\t%s\n"
                                              uu____5405 uu____5406);
                                       ret ut1)
                                   in
                                focus uu____5392)))
                      in
                   let uu____5407 = trytac' rewrite_eq  in
                   bind uu____5407
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
           let uu____5449 =
             match ps.FStar_Tactics_Types.goals with
             | g::gs -> (g, gs)
             | [] -> failwith "Pointwise: no goals"  in
           match uu____5449 with
           | (g,gs) ->
               let gt1 = g.FStar_Tactics_Types.goal_ty  in
               (log ps
                  (fun uu____5486  ->
                     let uu____5487 = FStar_Syntax_Print.term_to_string gt1
                        in
                     FStar_Util.print1 "Pointwise starting with %s\n"
                       uu____5487);
                bind dismiss_all
                  (fun uu____5490  ->
                     let uu____5491 =
                       tac_fold_env d
                         (pointwise_rec ps tau g.FStar_Tactics_Types.opts)
                         g.FStar_Tactics_Types.context gt1
                        in
                     bind uu____5491
                       (fun gt'  ->
                          log ps
                            (fun uu____5501  ->
                               let uu____5502 =
                                 FStar_Syntax_Print.term_to_string gt'  in
                               FStar_Util.print1
                                 "Pointwise seems to have succeded with %s\n"
                                 uu____5502);
                          (let uu____5503 = push_goals gs  in
                           bind uu____5503
                             (fun uu____5507  ->
                                add_goals
                                  [(let uu___103_5509 = g  in
                                    {
                                      FStar_Tactics_Types.context =
                                        (uu___103_5509.FStar_Tactics_Types.context);
                                      FStar_Tactics_Types.witness =
                                        (uu___103_5509.FStar_Tactics_Types.witness);
                                      FStar_Tactics_Types.goal_ty = gt';
                                      FStar_Tactics_Types.opts =
                                        (uu___103_5509.FStar_Tactics_Types.opts);
                                      FStar_Tactics_Types.is_guard =
                                        (uu___103_5509.FStar_Tactics_Types.is_guard)
                                    })]))))))
  
let (trefl : Prims.unit tac) =
  bind cur_goal
    (fun g  ->
       let uu____5531 =
         FStar_Syntax_Util.un_squash g.FStar_Tactics_Types.goal_ty  in
       match uu____5531 with
       | FStar_Pervasives_Native.Some t ->
           let uu____5543 = FStar_Syntax_Util.head_and_args' t  in
           (match uu____5543 with
            | (hd1,args) ->
                let uu____5576 =
                  let uu____5589 =
                    let uu____5590 = FStar_Syntax_Util.un_uinst hd1  in
                    uu____5590.FStar_Syntax_Syntax.n  in
                  (uu____5589, args)  in
                (match uu____5576 with
                 | (FStar_Syntax_Syntax.Tm_fvar
                    fv,uu____5604::(l,uu____5606)::(r,uu____5608)::[]) when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.eq2_lid
                     ->
                     let uu____5655 =
                       let uu____5656 =
                         do_unify g.FStar_Tactics_Types.context l r  in
                       Prims.op_Negation uu____5656  in
                     if uu____5655
                     then
                       let uu____5659 = tts g.FStar_Tactics_Types.context l
                          in
                       let uu____5660 = tts g.FStar_Tactics_Types.context r
                          in
                       fail2 "trefl: not a trivial equality (%s vs %s)"
                         uu____5659 uu____5660
                     else solve g FStar_Syntax_Util.exp_unit
                 | (hd2,uu____5663) ->
                     let uu____5680 = tts g.FStar_Tactics_Types.context t  in
                     fail1 "trefl: not an equality (%s)" uu____5680))
       | FStar_Pervasives_Native.None  -> fail "not an irrelevant goal")
  
let (dup : Prims.unit tac) =
  bind cur_goal
    (fun g  ->
       let uu____5690 =
         new_uvar "dup" g.FStar_Tactics_Types.context
           g.FStar_Tactics_Types.goal_ty
          in
       bind uu____5690
         (fun u  ->
            let g' =
              let uu___104_5697 = g  in
              {
                FStar_Tactics_Types.context =
                  (uu___104_5697.FStar_Tactics_Types.context);
                FStar_Tactics_Types.witness = u;
                FStar_Tactics_Types.goal_ty =
                  (uu___104_5697.FStar_Tactics_Types.goal_ty);
                FStar_Tactics_Types.opts =
                  (uu___104_5697.FStar_Tactics_Types.opts);
                FStar_Tactics_Types.is_guard =
                  (uu___104_5697.FStar_Tactics_Types.is_guard)
              }  in
            bind dismiss
              (fun uu____5700  ->
                 let uu____5701 =
                   let uu____5704 =
                     let uu____5705 =
                       FStar_TypeChecker_TcTerm.universe_of
                         g.FStar_Tactics_Types.context
                         g.FStar_Tactics_Types.goal_ty
                        in
                     FStar_Syntax_Util.mk_eq2 uu____5705
                       g.FStar_Tactics_Types.goal_ty u
                       g.FStar_Tactics_Types.witness
                      in
                   add_irrelevant_goal "dup equation"
                     g.FStar_Tactics_Types.context uu____5704
                     g.FStar_Tactics_Types.opts
                    in
                 bind uu____5701
                   (fun uu____5708  ->
                      let uu____5709 = add_goals [g']  in
                      bind uu____5709 (fun uu____5713  -> ret ())))))
  
let (flip : Prims.unit tac) =
  bind get
    (fun ps  ->
       match ps.FStar_Tactics_Types.goals with
       | g1::g2::gs ->
           set
             (let uu___105_5732 = ps  in
              {
                FStar_Tactics_Types.main_context =
                  (uu___105_5732.FStar_Tactics_Types.main_context);
                FStar_Tactics_Types.main_goal =
                  (uu___105_5732.FStar_Tactics_Types.main_goal);
                FStar_Tactics_Types.all_implicits =
                  (uu___105_5732.FStar_Tactics_Types.all_implicits);
                FStar_Tactics_Types.goals = (g2 :: g1 :: gs);
                FStar_Tactics_Types.smt_goals =
                  (uu___105_5732.FStar_Tactics_Types.smt_goals);
                FStar_Tactics_Types.depth =
                  (uu___105_5732.FStar_Tactics_Types.depth);
                FStar_Tactics_Types.__dump =
                  (uu___105_5732.FStar_Tactics_Types.__dump);
                FStar_Tactics_Types.psc =
                  (uu___105_5732.FStar_Tactics_Types.psc);
                FStar_Tactics_Types.entry_range =
                  (uu___105_5732.FStar_Tactics_Types.entry_range)
              })
       | uu____5733 -> fail "flip: less than 2 goals")
  
let (later : Prims.unit tac) =
  bind get
    (fun ps  ->
       match ps.FStar_Tactics_Types.goals with
       | [] -> ret ()
       | g::gs ->
           set
             (let uu___106_5750 = ps  in
              {
                FStar_Tactics_Types.main_context =
                  (uu___106_5750.FStar_Tactics_Types.main_context);
                FStar_Tactics_Types.main_goal =
                  (uu___106_5750.FStar_Tactics_Types.main_goal);
                FStar_Tactics_Types.all_implicits =
                  (uu___106_5750.FStar_Tactics_Types.all_implicits);
                FStar_Tactics_Types.goals = (FStar_List.append gs [g]);
                FStar_Tactics_Types.smt_goals =
                  (uu___106_5750.FStar_Tactics_Types.smt_goals);
                FStar_Tactics_Types.depth =
                  (uu___106_5750.FStar_Tactics_Types.depth);
                FStar_Tactics_Types.__dump =
                  (uu___106_5750.FStar_Tactics_Types.__dump);
                FStar_Tactics_Types.psc =
                  (uu___106_5750.FStar_Tactics_Types.psc);
                FStar_Tactics_Types.entry_range =
                  (uu___106_5750.FStar_Tactics_Types.entry_range)
              }))
  
let (qed : Prims.unit tac) =
  bind get
    (fun ps  ->
       match ps.FStar_Tactics_Types.goals with
       | [] -> ret ()
       | uu____5759 -> fail "Not done!")
  
let (cases :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 tac)
  =
  fun t  ->
    let uu____5777 =
      bind cur_goal
        (fun g  ->
           let uu____5791 = __tc g.FStar_Tactics_Types.context t  in
           bind uu____5791
             (fun uu____5827  ->
                match uu____5827 with
                | (t1,typ,guard) ->
                    let uu____5843 = FStar_Syntax_Util.head_and_args typ  in
                    (match uu____5843 with
                     | (hd1,args) ->
                         let uu____5886 =
                           let uu____5899 =
                             let uu____5900 = FStar_Syntax_Util.un_uinst hd1
                                in
                             uu____5900.FStar_Syntax_Syntax.n  in
                           (uu____5899, args)  in
                         (match uu____5886 with
                          | (FStar_Syntax_Syntax.Tm_fvar
                             fv,(p,uu____5919)::(q,uu____5921)::[]) when
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
                                let uu___107_5959 = g  in
                                let uu____5960 =
                                  FStar_TypeChecker_Env.push_bv
                                    g.FStar_Tactics_Types.context v_p
                                   in
                                {
                                  FStar_Tactics_Types.context = uu____5960;
                                  FStar_Tactics_Types.witness =
                                    (uu___107_5959.FStar_Tactics_Types.witness);
                                  FStar_Tactics_Types.goal_ty =
                                    (uu___107_5959.FStar_Tactics_Types.goal_ty);
                                  FStar_Tactics_Types.opts =
                                    (uu___107_5959.FStar_Tactics_Types.opts);
                                  FStar_Tactics_Types.is_guard =
                                    (uu___107_5959.FStar_Tactics_Types.is_guard)
                                }  in
                              let g2 =
                                let uu___108_5962 = g  in
                                let uu____5963 =
                                  FStar_TypeChecker_Env.push_bv
                                    g.FStar_Tactics_Types.context v_q
                                   in
                                {
                                  FStar_Tactics_Types.context = uu____5963;
                                  FStar_Tactics_Types.witness =
                                    (uu___108_5962.FStar_Tactics_Types.witness);
                                  FStar_Tactics_Types.goal_ty =
                                    (uu___108_5962.FStar_Tactics_Types.goal_ty);
                                  FStar_Tactics_Types.opts =
                                    (uu___108_5962.FStar_Tactics_Types.opts);
                                  FStar_Tactics_Types.is_guard =
                                    (uu___108_5962.FStar_Tactics_Types.is_guard)
                                }  in
                              bind dismiss
                                (fun uu____5970  ->
                                   let uu____5971 = add_goals [g1; g2]  in
                                   bind uu____5971
                                     (fun uu____5980  ->
                                        let uu____5981 =
                                          let uu____5986 =
                                            FStar_Syntax_Syntax.bv_to_name
                                              v_p
                                             in
                                          let uu____5987 =
                                            FStar_Syntax_Syntax.bv_to_name
                                              v_q
                                             in
                                          (uu____5986, uu____5987)  in
                                        ret uu____5981))
                          | uu____5992 ->
                              let uu____6005 =
                                tts g.FStar_Tactics_Types.context typ  in
                              fail1 "Not a disjunction: %s" uu____6005))))
       in
    FStar_All.pipe_left (wrap_err "cases") uu____5777
  
let (set_options : Prims.string -> Prims.unit tac) =
  fun s  ->
    bind cur_goal
      (fun g  ->
         FStar_Options.push ();
         (let uu____6043 = FStar_Util.smap_copy g.FStar_Tactics_Types.opts
             in
          FStar_Options.set uu____6043);
         (let res = FStar_Options.set_options FStar_Options.Set s  in
          let opts' = FStar_Options.peek ()  in
          FStar_Options.pop ();
          (match res with
           | FStar_Getopt.Success  ->
               let g' =
                 let uu___109_6050 = g  in
                 {
                   FStar_Tactics_Types.context =
                     (uu___109_6050.FStar_Tactics_Types.context);
                   FStar_Tactics_Types.witness =
                     (uu___109_6050.FStar_Tactics_Types.witness);
                   FStar_Tactics_Types.goal_ty =
                     (uu___109_6050.FStar_Tactics_Types.goal_ty);
                   FStar_Tactics_Types.opts = opts';
                   FStar_Tactics_Types.is_guard =
                     (uu___109_6050.FStar_Tactics_Types.is_guard)
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
      let uu____6094 =
        bind cur_goal
          (fun goal  ->
             let env =
               FStar_TypeChecker_Env.set_expected_typ
                 goal.FStar_Tactics_Types.context ty
                in
             let uu____6102 = __tc env tm  in
             bind uu____6102
               (fun uu____6122  ->
                  match uu____6122 with
                  | (tm1,typ,guard) ->
                      (FStar_TypeChecker_Rel.force_trivial_guard env guard;
                       ret tm1)))
         in
      FStar_All.pipe_left (wrap_err "unquote") uu____6094
  
let (uvar_env :
  env ->
    FStar_Syntax_Syntax.typ FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.term tac)
  =
  fun env  ->
    fun ty  ->
      let uu____6153 =
        match ty with
        | FStar_Pervasives_Native.Some ty1 -> ret ty1
        | FStar_Pervasives_Native.None  ->
            let uu____6159 =
              let uu____6160 = FStar_Syntax_Util.type_u ()  in
              FStar_All.pipe_left FStar_Pervasives_Native.fst uu____6160  in
            new_uvar "uvar_env.2" env uu____6159
         in
      bind uu____6153
        (fun typ  ->
           let uu____6172 = new_uvar "uvar_env" env typ  in
           bind uu____6172 (fun t  -> ret t))
  
let (unshelve : FStar_Syntax_Syntax.term -> Prims.unit tac) =
  fun t  ->
    let uu____6184 =
      bind cur_goal
        (fun goal  ->
           let uu____6190 = __tc goal.FStar_Tactics_Types.context t  in
           bind uu____6190
             (fun uu____6210  ->
                match uu____6210 with
                | (t1,typ,guard) ->
                    let uu____6222 =
                      must_trivial goal.FStar_Tactics_Types.context guard  in
                    bind uu____6222
                      (fun uu____6227  ->
                         let uu____6228 =
                           let uu____6231 =
                             let uu___110_6232 = goal  in
                             let uu____6233 =
                               bnorm goal.FStar_Tactics_Types.context t1  in
                             let uu____6234 =
                               bnorm goal.FStar_Tactics_Types.context typ  in
                             {
                               FStar_Tactics_Types.context =
                                 (uu___110_6232.FStar_Tactics_Types.context);
                               FStar_Tactics_Types.witness = uu____6233;
                               FStar_Tactics_Types.goal_ty = uu____6234;
                               FStar_Tactics_Types.opts =
                                 (uu___110_6232.FStar_Tactics_Types.opts);
                               FStar_Tactics_Types.is_guard = false
                             }  in
                           [uu____6231]  in
                         add_goals uu____6228)))
       in
    FStar_All.pipe_left (wrap_err "unshelve") uu____6184
  
let (unify :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool tac) =
  fun t1  ->
    fun t2  ->
      bind get
        (fun ps  ->
           let uu____6252 =
             do_unify ps.FStar_Tactics_Types.main_context t1 t2  in
           ret uu____6252)
  
let (launch_process :
  Prims.string -> Prims.string -> Prims.string -> Prims.string tac) =
  fun prog  ->
    fun args  ->
      fun input  ->
        bind idtac
          (fun uu____6269  ->
             let uu____6270 = FStar_Options.unsafe_tactic_exec ()  in
             if uu____6270
             then
               let s =
                 FStar_Util.launch_process true "tactic_launch" prog args
                   input (fun uu____6276  -> fun uu____6277  -> false)
                  in
               ret s
             else
               fail
                 "launch_process: will not run anything unless --unsafe_tactic_exec is provided")
  
let (fresh_binder_named :
  Prims.string -> FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.binder tac)
  =
  fun nm  ->
    fun t  ->
      bind idtac
        (fun uu____6297  ->
           let uu____6298 =
             let uu____6305 =
               FStar_Syntax_Syntax.gen_bv nm FStar_Pervasives_Native.None t
                in
             (uu____6305, FStar_Pervasives_Native.None)  in
           ret uu____6298)
  
let (goal_of_goal_ty :
  env ->
    FStar_Syntax_Syntax.typ ->
      (FStar_Tactics_Types.goal,FStar_TypeChecker_Env.guard_t)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun typ  ->
      let uu____6328 =
        FStar_TypeChecker_Util.new_implicit_var "proofstate_of_goal_ty"
          typ.FStar_Syntax_Syntax.pos env typ
         in
      match uu____6328 with
      | (u,uu____6346,g_u) ->
          let g =
            let uu____6361 = FStar_Options.peek ()  in
            {
              FStar_Tactics_Types.context = env;
              FStar_Tactics_Types.witness = u;
              FStar_Tactics_Types.goal_ty = typ;
              FStar_Tactics_Types.opts = uu____6361;
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
      let uu____6372 = goal_of_goal_ty env typ  in
      match uu____6372 with
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
  