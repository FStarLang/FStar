open Prims
type name = FStar_Syntax_Syntax.bv[@@deriving show]
type env = FStar_TypeChecker_Env.env[@@deriving show]
type implicits = FStar_TypeChecker_Env.implicits[@@deriving show]
let normalize :
  FStar_TypeChecker_Normalize.step Prims.list ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun s  ->
    fun e  ->
      fun t  ->
        FStar_TypeChecker_Normalize.normalize_with_primitive_steps
          FStar_Reflection_Interpreter.reflection_primops s e t
  
let bnorm :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  = fun e  -> fun t  -> normalize [] e t 
let tts :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> Prims.string =
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
  'Auu____79 .
    'Auu____79 tac ->
      FStar_Tactics_Types.proofstate ->
        'Auu____79 FStar_Tactics_Result.__result
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
  
let idtac : Prims.unit tac = ret () 
let goal_to_string : FStar_Tactics_Types.goal -> Prims.string =
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
  
let tacprint : Prims.string -> Prims.unit =
  fun s  -> FStar_Util.print1 "TAC>> %s\n" s 
let tacprint1 : Prims.string -> Prims.string -> Prims.unit =
  fun s  ->
    fun x  ->
      let uu____172 = FStar_Util.format1 s x  in
      FStar_Util.print1 "TAC>> %s\n" uu____172
  
let tacprint2 : Prims.string -> Prims.string -> Prims.string -> Prims.unit =
  fun s  ->
    fun x  ->
      fun y  ->
        let uu____182 = FStar_Util.format2 s x y  in
        FStar_Util.print1 "TAC>> %s\n" uu____182
  
let tacprint3 :
  Prims.string -> Prims.string -> Prims.string -> Prims.string -> Prims.unit
  =
  fun s  ->
    fun x  ->
      fun y  ->
        fun z  ->
          let uu____195 = FStar_Util.format3 s x y z  in
          FStar_Util.print1 "TAC>> %s\n" uu____195
  
let comp_to_typ : FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.typ =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total (t,uu____200) -> t
    | FStar_Syntax_Syntax.GTotal (t,uu____210) -> t
    | FStar_Syntax_Syntax.Comp ct -> ct.FStar_Syntax_Syntax.result_typ
  
let is_irrelevant : FStar_Tactics_Types.goal -> Prims.bool =
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
  
let dump_cur : FStar_Tactics_Types.proofstate -> Prims.string -> Prims.unit =
  fun ps  ->
    fun msg  ->
      match ps.FStar_Tactics_Types.goals with
      | [] -> tacprint1 "No more goals (%s)" msg
      | h::uu____260 ->
          (tacprint1 "Current goal (%s):" msg;
           (let uu____264 = FStar_List.hd ps.FStar_Tactics_Types.goals  in
            dump_goal ps uu____264))
  
let ps_to_string :
  (Prims.string,FStar_Tactics_Types.proofstate)
    FStar_Pervasives_Native.tuple2 -> Prims.string
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
  
let goal_to_json : FStar_Tactics_Types.goal -> FStar_Util.json =
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
  
let ps_to_json :
  (Prims.string,FStar_Tactics_Types.proofstate)
    FStar_Pervasives_Native.tuple2 -> FStar_Util.json
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
  
let dump_proofstate :
  FStar_Tactics_Types.proofstate -> Prims.string -> Prims.unit =
  fun ps  ->
    fun msg  ->
      FStar_Options.with_saved_options
        (fun uu____459  ->
           FStar_Options.set_option "print_effect_args"
             (FStar_Options.Bool true);
           FStar_Util.print_generic "proof-state" ps_to_string ps_to_json
             (msg, ps))
  
let print_proof_state1 : Prims.string -> Prims.unit tac =
  fun msg  ->
    mk_tac
      (fun ps  ->
         let psc = ps.FStar_Tactics_Types.psc  in
         let subst1 = FStar_TypeChecker_Normalize.psc_subst psc  in
         (let uu____480 = FStar_Tactics_Types.subst_proof_state subst1 ps  in
          dump_cur uu____480 msg);
         FStar_Tactics_Result.Success ((), ps))
  
let print_proof_state : Prims.string -> Prims.unit tac =
  fun msg  ->
    mk_tac
      (fun ps  ->
         let psc = ps.FStar_Tactics_Types.psc  in
         let subst1 = FStar_TypeChecker_Normalize.psc_subst psc  in
         (let uu____496 = FStar_Tactics_Types.subst_proof_state subst1 ps  in
          dump_proofstate uu____496 msg);
         FStar_Tactics_Result.Success ((), ps))
  
let get : FStar_Tactics_Types.proofstate tac =
  mk_tac (fun p  -> FStar_Tactics_Result.Success (p, p)) 
let tac_verb_dbg : Prims.bool FStar_Pervasives_Native.option FStar_ST.ref =
  FStar_Util.mk_ref FStar_Pervasives_Native.None 
let rec log :
  FStar_Tactics_Types.proofstate -> (Prims.unit -> Prims.unit) -> Prims.unit
  =
  fun ps  ->
    fun f  ->
      let uu____525 = FStar_ST.op_Bang tac_verb_dbg  in
      match uu____525 with
      | FStar_Pervasives_Native.None  ->
          ((let uu____581 =
              let uu____584 =
                FStar_TypeChecker_Env.debug
                  ps.FStar_Tactics_Types.main_context
                  (FStar_Options.Other "TacVerbose")
                 in
              FStar_Pervasives_Native.Some uu____584  in
            FStar_ST.op_Colon_Equals tac_verb_dbg uu____581);
           log ps f)
      | FStar_Pervasives_Native.Some (true ) -> f ()
      | FStar_Pervasives_Native.Some (false ) -> ()
  
let mlog :
  'a . (Prims.unit -> Prims.unit) -> (Prims.unit -> 'a tac) -> 'a tac =
  fun f  -> fun cont  -> bind get (fun ps  -> log ps f; cont ()) 
let fail : 'Auu____671 . Prims.string -> 'Auu____671 tac =
  fun msg  ->
    mk_tac
      (fun ps  ->
         (let uu____682 =
            FStar_TypeChecker_Env.debug ps.FStar_Tactics_Types.main_context
              (FStar_Options.Other "TacFail")
             in
          if uu____682
          then dump_proofstate ps (Prims.strcat "TACTING FAILING: " msg)
          else ());
         FStar_Tactics_Result.Failed (msg, ps))
  
let fail1 : 'Auu____687 . Prims.string -> Prims.string -> 'Auu____687 tac =
  fun msg  ->
    fun x  -> let uu____698 = FStar_Util.format1 msg x  in fail uu____698
  
let fail2 :
  'Auu____703 .
    Prims.string -> Prims.string -> Prims.string -> 'Auu____703 tac
  =
  fun msg  ->
    fun x  ->
      fun y  -> let uu____718 = FStar_Util.format2 msg x y  in fail uu____718
  
let fail3 :
  'Auu____724 .
    Prims.string ->
      Prims.string -> Prims.string -> Prims.string -> 'Auu____724 tac
  =
  fun msg  ->
    fun x  ->
      fun y  ->
        fun z  ->
          let uu____743 = FStar_Util.format3 msg x y z  in fail uu____743
  
let trytac' : 'a . 'a tac -> (Prims.string,'a) FStar_Util.either tac =
  fun t  ->
    mk_tac
      (fun ps  ->
         let tx = FStar_Syntax_Unionfind.new_transaction ()  in
         let uu____773 = run t ps  in
         match uu____773 with
         | FStar_Tactics_Result.Success (a,q) ->
             (FStar_Syntax_Unionfind.commit tx;
              FStar_Tactics_Result.Success ((FStar_Util.Inr a), q))
         | FStar_Tactics_Result.Failed (m,uu____794) ->
             (FStar_Syntax_Unionfind.rollback tx;
              FStar_Tactics_Result.Success ((FStar_Util.Inl m), ps)))
  
let trytac : 'a . 'a tac -> 'a FStar_Pervasives_Native.option tac =
  fun t  ->
    let uu____819 = trytac' t  in
    bind uu____819
      (fun r  ->
         match r with
         | FStar_Util.Inr v1 -> ret (FStar_Pervasives_Native.Some v1)
         | FStar_Util.Inl uu____846 -> ret FStar_Pervasives_Native.None)
  
let wrap_err : 'a . Prims.string -> 'a tac -> 'a tac =
  fun pref  ->
    fun t  ->
      mk_tac
        (fun ps  ->
           let uu____872 = run t ps  in
           match uu____872 with
           | FStar_Tactics_Result.Success (a,q) ->
               FStar_Tactics_Result.Success (a, q)
           | FStar_Tactics_Result.Failed (msg,q) ->
               FStar_Tactics_Result.Failed
                 ((Prims.strcat pref (Prims.strcat ": " msg)), q))
  
let set : FStar_Tactics_Types.proofstate -> Prims.unit tac =
  fun p  -> mk_tac (fun uu____889  -> FStar_Tactics_Result.Success ((), p)) 
let do_unify :
  env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let debug_on uu____902 =
          let uu____903 =
            FStar_Options.set_options FStar_Options.Set
              "--debug_level Rel --debug_level RelCheck"
             in
          ()  in
        let debug_off uu____907 =
          let uu____908 = FStar_Options.set_options FStar_Options.Reset ""
             in
          ()  in
        (let uu____910 =
           FStar_TypeChecker_Env.debug env (FStar_Options.Other "1346")  in
         if uu____910
         then
           (debug_on ();
            (let uu____912 = FStar_Syntax_Print.term_to_string t1  in
             let uu____913 = FStar_Syntax_Print.term_to_string t2  in
             FStar_Util.print2 "%%%%%%%%do_unify %s =? %s\n" uu____912
               uu____913))
         else ());
        (try
           let res = FStar_TypeChecker_Rel.teq_nosmt env t1 t2  in
           debug_off (); res
         with | uu____900_925 -> (debug_off (); false))
  
let trysolve :
  FStar_Tactics_Types.goal -> FStar_Syntax_Syntax.term -> Prims.bool =
  fun goal  ->
    fun solution  ->
      do_unify goal.FStar_Tactics_Types.context solution
        goal.FStar_Tactics_Types.witness
  
let dismiss : Prims.unit tac =
  bind get
    (fun p  ->
       let uu____938 =
         let uu___291_939 = p  in
         let uu____940 = FStar_List.tl p.FStar_Tactics_Types.goals  in
         {
           FStar_Tactics_Types.main_context =
             (uu___291_939.FStar_Tactics_Types.main_context);
           FStar_Tactics_Types.main_goal =
             (uu___291_939.FStar_Tactics_Types.main_goal);
           FStar_Tactics_Types.all_implicits =
             (uu___291_939.FStar_Tactics_Types.all_implicits);
           FStar_Tactics_Types.goals = uu____940;
           FStar_Tactics_Types.smt_goals =
             (uu___291_939.FStar_Tactics_Types.smt_goals);
           FStar_Tactics_Types.depth =
             (uu___291_939.FStar_Tactics_Types.depth);
           FStar_Tactics_Types.__dump =
             (uu___291_939.FStar_Tactics_Types.__dump);
           FStar_Tactics_Types.psc = (uu___291_939.FStar_Tactics_Types.psc);
           FStar_Tactics_Types.entry_range =
             (uu___291_939.FStar_Tactics_Types.entry_range)
         }  in
       set uu____938)
  
let solve :
  FStar_Tactics_Types.goal -> FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun goal  ->
    fun solution  ->
      let uu____953 = trysolve goal solution  in
      if uu____953
      then dismiss
      else
        (let uu____957 =
           let uu____958 = tts goal.FStar_Tactics_Types.context solution  in
           let uu____959 =
             tts goal.FStar_Tactics_Types.context
               goal.FStar_Tactics_Types.witness
              in
           let uu____960 =
             tts goal.FStar_Tactics_Types.context
               goal.FStar_Tactics_Types.goal_ty
              in
           FStar_Util.format3 "%s does not solve %s : %s" uu____958 uu____959
             uu____960
            in
         fail uu____957)
  
let dismiss_all : Prims.unit tac =
  bind get
    (fun p  ->
       set
         (let uu___292_967 = p  in
          {
            FStar_Tactics_Types.main_context =
              (uu___292_967.FStar_Tactics_Types.main_context);
            FStar_Tactics_Types.main_goal =
              (uu___292_967.FStar_Tactics_Types.main_goal);
            FStar_Tactics_Types.all_implicits =
              (uu___292_967.FStar_Tactics_Types.all_implicits);
            FStar_Tactics_Types.goals = [];
            FStar_Tactics_Types.smt_goals =
              (uu___292_967.FStar_Tactics_Types.smt_goals);
            FStar_Tactics_Types.depth =
              (uu___292_967.FStar_Tactics_Types.depth);
            FStar_Tactics_Types.__dump =
              (uu___292_967.FStar_Tactics_Types.__dump);
            FStar_Tactics_Types.psc = (uu___292_967.FStar_Tactics_Types.psc);
            FStar_Tactics_Types.entry_range =
              (uu___292_967.FStar_Tactics_Types.entry_range)
          }))
  
let nwarn : Prims.int FStar_ST.ref = FStar_Util.mk_ref (Prims.parse_int "0") 
let check_valid_goal : FStar_Tactics_Types.goal -> Prims.unit =
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
      let uu____991 = FStar_TypeChecker_Env.pop_bv e  in
      match uu____991 with
      | FStar_Pervasives_Native.None  -> b3
      | FStar_Pervasives_Native.Some (bv,e1) ->
          let b4 =
            b3 &&
              (FStar_TypeChecker_Env.closed e1 bv.FStar_Syntax_Syntax.sort)
             in
          aux b4 e1
       in
    let uu____1009 =
      (let uu____1012 = aux b2 env  in Prims.op_Negation uu____1012) &&
        (let uu____1014 = FStar_ST.op_Bang nwarn  in
         uu____1014 < (Prims.parse_int "5"))
       in
    if uu____1009
    then
      ((let uu____1064 =
          let uu____1069 =
            let uu____1070 = goal_to_string g  in
            FStar_Util.format1
              "The following goal is ill-formed. Keeping calm and carrying on...\n<%s>\n\n"
              uu____1070
             in
          (FStar_Errors.Warning_IllFormedGoal, uu____1069)  in
        FStar_Errors.log_issue
          (g.FStar_Tactics_Types.goal_ty).FStar_Syntax_Syntax.pos uu____1064);
       (let uu____1071 =
          let uu____1072 = FStar_ST.op_Bang nwarn  in
          uu____1072 + (Prims.parse_int "1")  in
        FStar_ST.op_Colon_Equals nwarn uu____1071))
    else ()
  
let add_goals : FStar_Tactics_Types.goal Prims.list -> Prims.unit tac =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___293_1187 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___293_1187.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___293_1187.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___293_1187.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (FStar_List.append gs p.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___293_1187.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___293_1187.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___293_1187.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___293_1187.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___293_1187.FStar_Tactics_Types.entry_range)
            }))
  
let add_smt_goals : FStar_Tactics_Types.goal Prims.list -> Prims.unit tac =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___294_1205 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___294_1205.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___294_1205.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___294_1205.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___294_1205.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (FStar_List.append gs p.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___294_1205.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___294_1205.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___294_1205.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___294_1205.FStar_Tactics_Types.entry_range)
            }))
  
let push_goals : FStar_Tactics_Types.goal Prims.list -> Prims.unit tac =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___295_1223 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___295_1223.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___295_1223.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___295_1223.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (FStar_List.append p.FStar_Tactics_Types.goals gs);
              FStar_Tactics_Types.smt_goals =
                (uu___295_1223.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___295_1223.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___295_1223.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___295_1223.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___295_1223.FStar_Tactics_Types.entry_range)
            }))
  
let push_smt_goals : FStar_Tactics_Types.goal Prims.list -> Prims.unit tac =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___296_1241 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___296_1241.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___296_1241.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___296_1241.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___296_1241.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (FStar_List.append p.FStar_Tactics_Types.smt_goals gs);
              FStar_Tactics_Types.depth =
                (uu___296_1241.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___296_1241.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___296_1241.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___296_1241.FStar_Tactics_Types.entry_range)
            }))
  
let replace_cur : FStar_Tactics_Types.goal -> Prims.unit tac =
  fun g  -> bind dismiss (fun uu____1250  -> add_goals [g]) 
let add_implicits : implicits -> Prims.unit tac =
  fun i  ->
    bind get
      (fun p  ->
         set
           (let uu___297_1262 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___297_1262.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___297_1262.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (FStar_List.append i p.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___297_1262.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___297_1262.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___297_1262.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___297_1262.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___297_1262.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___297_1262.FStar_Tactics_Types.entry_range)
            }))
  
let new_uvar :
  Prims.string ->
    env -> FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.term tac
  =
  fun reason  ->
    fun env  ->
      fun typ  ->
        let uu____1288 =
          FStar_TypeChecker_Util.new_implicit_var reason
            typ.FStar_Syntax_Syntax.pos env typ
           in
        match uu____1288 with
        | (u,uu____1304,g_u) ->
            let uu____1318 =
              add_implicits g_u.FStar_TypeChecker_Env.implicits  in
            bind uu____1318 (fun uu____1322  -> ret u)
  
let is_true : FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____1326 = FStar_Syntax_Util.un_squash t  in
    match uu____1326 with
    | FStar_Pervasives_Native.Some t' ->
        let uu____1336 =
          let uu____1337 = FStar_Syntax_Subst.compress t'  in
          uu____1337.FStar_Syntax_Syntax.n  in
        (match uu____1336 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.true_lid
         | uu____1341 -> false)
    | uu____1342 -> false
  
let is_false : FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____1350 = FStar_Syntax_Util.un_squash t  in
    match uu____1350 with
    | FStar_Pervasives_Native.Some t' ->
        let uu____1360 =
          let uu____1361 = FStar_Syntax_Subst.compress t'  in
          uu____1361.FStar_Syntax_Syntax.n  in
        (match uu____1360 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.false_lid
         | uu____1365 -> false)
    | uu____1366 -> false
  
let cur_goal : FStar_Tactics_Types.goal tac =
  bind get
    (fun p  ->
       match p.FStar_Tactics_Types.goals with
       | [] -> fail "No more goals (1)"
       | hd1::tl1 -> ret hd1)
  
let is_guard : Prims.bool tac =
  bind cur_goal (fun g  -> ret g.FStar_Tactics_Types.is_guard) 
let mk_irrelevant_goal :
  Prims.string ->
    env ->
      FStar_Syntax_Syntax.typ ->
        FStar_Options.optionstate -> FStar_Tactics_Types.goal tac
  =
  fun reason  ->
    fun env  ->
      fun phi  ->
        fun opts  ->
          let typ =
            let uu____1404 = env.FStar_TypeChecker_Env.universe_of env phi
               in
            FStar_Syntax_Util.mk_squash uu____1404 phi  in
          let uu____1405 = new_uvar reason env typ  in
          bind uu____1405
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
  
let __tc :
  env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.typ,FStar_TypeChecker_Env.guard_t)
        FStar_Pervasives_Native.tuple3 tac
  =
  fun e  ->
    fun t  ->
      bind get
        (fun ps  ->
           try
             let uu____1461 =
               (ps.FStar_Tactics_Types.main_context).FStar_TypeChecker_Env.type_of
                 e t
                in
             ret uu____1461
           with | e1 -> fail "not typeable")
  
let must_trivial : env -> FStar_TypeChecker_Env.guard_t -> Prims.unit tac =
  fun e  ->
    fun g  ->
      try
        let uu____1509 =
          let uu____1510 =
            let uu____1511 = FStar_TypeChecker_Rel.discharge_guard_no_smt e g
               in
            FStar_All.pipe_left FStar_TypeChecker_Rel.is_trivial uu____1511
             in
          Prims.op_Negation uu____1510  in
        if uu____1509 then fail "got non-trivial guard" else ret ()
      with | uu____1520 -> fail "got non-trivial guard"
  
let tc : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.typ tac =
  fun t  ->
    let uu____1528 =
      bind cur_goal
        (fun goal  ->
           let uu____1534 = __tc goal.FStar_Tactics_Types.context t  in
           bind uu____1534
             (fun uu____1554  ->
                match uu____1554 with
                | (t1,typ,guard) ->
                    let uu____1566 =
                      must_trivial goal.FStar_Tactics_Types.context guard  in
                    bind uu____1566 (fun uu____1570  -> ret typ)))
       in
    FStar_All.pipe_left (wrap_err "tc") uu____1528
  
let add_irrelevant_goal :
  Prims.string ->
    env ->
      FStar_Syntax_Syntax.typ -> FStar_Options.optionstate -> Prims.unit tac
  =
  fun reason  ->
    fun env  ->
      fun phi  ->
        fun opts  ->
          let uu____1591 = mk_irrelevant_goal reason env phi opts  in
          bind uu____1591 (fun goal  -> add_goals [goal])
  
let istrivial : env -> FStar_Syntax_Syntax.term -> Prims.bool =
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
  
let trivial : Prims.unit tac =
  bind cur_goal
    (fun goal  ->
       let uu____1611 =
         istrivial goal.FStar_Tactics_Types.context
           goal.FStar_Tactics_Types.goal_ty
          in
       if uu____1611
       then solve goal FStar_Syntax_Util.exp_unit
       else
         (let uu____1615 =
            tts goal.FStar_Tactics_Types.context
              goal.FStar_Tactics_Types.goal_ty
             in
          fail1 "Not a trivial goal: %s" uu____1615))
  
let add_goal_from_guard :
  Prims.string ->
    env ->
      FStar_TypeChecker_Env.guard_t ->
        FStar_Options.optionstate -> Prims.unit tac
  =
  fun reason  ->
    fun e  ->
      fun g  ->
        fun opts  ->
          let uu____1632 =
            let uu____1633 = FStar_TypeChecker_Rel.simplify_guard e g  in
            uu____1633.FStar_TypeChecker_Env.guard_f  in
          match uu____1632 with
          | FStar_TypeChecker_Common.Trivial  -> ret ()
          | FStar_TypeChecker_Common.NonTrivial f ->
              let uu____1637 = istrivial e f  in
              if uu____1637
              then ret ()
              else
                (let uu____1641 = mk_irrelevant_goal reason e f opts  in
                 bind uu____1641
                   (fun goal  ->
                      let goal1 =
                        let uu___302_1648 = goal  in
                        {
                          FStar_Tactics_Types.context =
                            (uu___302_1648.FStar_Tactics_Types.context);
                          FStar_Tactics_Types.witness =
                            (uu___302_1648.FStar_Tactics_Types.witness);
                          FStar_Tactics_Types.goal_ty =
                            (uu___302_1648.FStar_Tactics_Types.goal_ty);
                          FStar_Tactics_Types.opts =
                            (uu___302_1648.FStar_Tactics_Types.opts);
                          FStar_Tactics_Types.is_guard = true
                        }  in
                      push_goals [goal1]))
  
let goal_from_guard :
  Prims.string ->
    env ->
      FStar_TypeChecker_Env.guard_t ->
        FStar_Options.optionstate ->
          FStar_Tactics_Types.goal FStar_Pervasives_Native.option tac
  =
  fun reason  ->
    fun e  ->
      fun g  ->
        fun opts  ->
          let uu____1669 =
            let uu____1670 = FStar_TypeChecker_Rel.simplify_guard e g  in
            uu____1670.FStar_TypeChecker_Env.guard_f  in
          match uu____1669 with
          | FStar_TypeChecker_Common.Trivial  ->
              ret FStar_Pervasives_Native.None
          | FStar_TypeChecker_Common.NonTrivial f ->
              let uu____1678 = istrivial e f  in
              if uu____1678
              then ret FStar_Pervasives_Native.None
              else
                (let uu____1686 = mk_irrelevant_goal reason e f opts  in
                 bind uu____1686
                   (fun goal  ->
                      ret
                        (FStar_Pervasives_Native.Some
                           (let uu___303_1696 = goal  in
                            {
                              FStar_Tactics_Types.context =
                                (uu___303_1696.FStar_Tactics_Types.context);
                              FStar_Tactics_Types.witness =
                                (uu___303_1696.FStar_Tactics_Types.witness);
                              FStar_Tactics_Types.goal_ty =
                                (uu___303_1696.FStar_Tactics_Types.goal_ty);
                              FStar_Tactics_Types.opts =
                                (uu___303_1696.FStar_Tactics_Types.opts);
                              FStar_Tactics_Types.is_guard = true
                            }))))
  
let smt : Prims.unit tac =
  bind cur_goal
    (fun g  ->
       let uu____1702 = is_irrelevant g  in
       if uu____1702
       then bind dismiss (fun uu____1706  -> add_smt_goals [g])
       else
         (let uu____1708 =
            tts g.FStar_Tactics_Types.context g.FStar_Tactics_Types.goal_ty
             in
          fail1 "goal is not irrelevant: cannot dispatch to smt (%s)"
            uu____1708))
  
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
             let uu____1749 =
               try
                 let uu____1783 =
                   let uu____1792 = FStar_BigInt.to_int_fs n1  in
                   FStar_List.splitAt uu____1792 p.FStar_Tactics_Types.goals
                    in
                 ret uu____1783
               with | uu____1814 -> fail "divide: not enough goals"  in
             bind uu____1749
               (fun uu____1841  ->
                  match uu____1841 with
                  | (lgs,rgs) ->
                      let lp =
                        let uu___304_1867 = p  in
                        {
                          FStar_Tactics_Types.main_context =
                            (uu___304_1867.FStar_Tactics_Types.main_context);
                          FStar_Tactics_Types.main_goal =
                            (uu___304_1867.FStar_Tactics_Types.main_goal);
                          FStar_Tactics_Types.all_implicits =
                            (uu___304_1867.FStar_Tactics_Types.all_implicits);
                          FStar_Tactics_Types.goals = lgs;
                          FStar_Tactics_Types.smt_goals = [];
                          FStar_Tactics_Types.depth =
                            (uu___304_1867.FStar_Tactics_Types.depth);
                          FStar_Tactics_Types.__dump =
                            (uu___304_1867.FStar_Tactics_Types.__dump);
                          FStar_Tactics_Types.psc =
                            (uu___304_1867.FStar_Tactics_Types.psc);
                          FStar_Tactics_Types.entry_range =
                            (uu___304_1867.FStar_Tactics_Types.entry_range)
                        }  in
                      let rp =
                        let uu___305_1869 = p  in
                        {
                          FStar_Tactics_Types.main_context =
                            (uu___305_1869.FStar_Tactics_Types.main_context);
                          FStar_Tactics_Types.main_goal =
                            (uu___305_1869.FStar_Tactics_Types.main_goal);
                          FStar_Tactics_Types.all_implicits =
                            (uu___305_1869.FStar_Tactics_Types.all_implicits);
                          FStar_Tactics_Types.goals = rgs;
                          FStar_Tactics_Types.smt_goals = [];
                          FStar_Tactics_Types.depth =
                            (uu___305_1869.FStar_Tactics_Types.depth);
                          FStar_Tactics_Types.__dump =
                            (uu___305_1869.FStar_Tactics_Types.__dump);
                          FStar_Tactics_Types.psc =
                            (uu___305_1869.FStar_Tactics_Types.psc);
                          FStar_Tactics_Types.entry_range =
                            (uu___305_1869.FStar_Tactics_Types.entry_range)
                        }  in
                      let uu____1870 = set lp  in
                      bind uu____1870
                        (fun uu____1878  ->
                           bind l
                             (fun a  ->
                                bind get
                                  (fun lp'  ->
                                     let uu____1892 = set rp  in
                                     bind uu____1892
                                       (fun uu____1900  ->
                                          bind r
                                            (fun b  ->
                                               bind get
                                                 (fun rp'  ->
                                                    let p' =
                                                      let uu___306_1916 = p
                                                         in
                                                      {
                                                        FStar_Tactics_Types.main_context
                                                          =
                                                          (uu___306_1916.FStar_Tactics_Types.main_context);
                                                        FStar_Tactics_Types.main_goal
                                                          =
                                                          (uu___306_1916.FStar_Tactics_Types.main_goal);
                                                        FStar_Tactics_Types.all_implicits
                                                          =
                                                          (uu___306_1916.FStar_Tactics_Types.all_implicits);
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
                                                          (uu___306_1916.FStar_Tactics_Types.depth);
                                                        FStar_Tactics_Types.__dump
                                                          =
                                                          (uu___306_1916.FStar_Tactics_Types.__dump);
                                                        FStar_Tactics_Types.psc
                                                          =
                                                          (uu___306_1916.FStar_Tactics_Types.psc);
                                                        FStar_Tactics_Types.entry_range
                                                          =
                                                          (uu___306_1916.FStar_Tactics_Types.entry_range)
                                                      }  in
                                                    let uu____1917 = set p'
                                                       in
                                                    bind uu____1917
                                                      (fun uu____1925  ->
                                                         ret (a, b))))))))))
  
let focus : 'a . 'a tac -> 'a tac =
  fun f  ->
    let uu____1943 = divide FStar_BigInt.one f idtac  in
    bind uu____1943
      (fun uu____1956  -> match uu____1956 with | (a,()) -> ret a)
  
let rec map : 'a . 'a tac -> 'a Prims.list tac =
  fun tau  ->
    bind get
      (fun p  ->
         match p.FStar_Tactics_Types.goals with
         | [] -> ret []
         | uu____1990::uu____1991 ->
             let uu____1994 =
               let uu____2003 = map tau  in
               divide FStar_BigInt.one tau uu____2003  in
             bind uu____1994
               (fun uu____2021  ->
                  match uu____2021 with | (h,t) -> ret (h :: t)))
  
let seq : Prims.unit tac -> Prims.unit tac -> Prims.unit tac =
  fun t1  ->
    fun t2  ->
      let uu____2058 =
        bind t1
          (fun uu____2063  ->
             let uu____2064 = map t2  in
             bind uu____2064 (fun uu____2072  -> ret ()))
         in
      focus uu____2058
  
let intro : FStar_Syntax_Syntax.binder tac =
  bind cur_goal
    (fun goal  ->
       let uu____2083 =
         FStar_Syntax_Util.arrow_one goal.FStar_Tactics_Types.goal_ty  in
       match uu____2083 with
       | FStar_Pervasives_Native.Some (b,c) ->
           let uu____2098 =
             let uu____2099 = FStar_Syntax_Util.is_total_comp c  in
             Prims.op_Negation uu____2099  in
           if uu____2098
           then fail "Codomain is effectful"
           else
             (let env' =
                FStar_TypeChecker_Env.push_binders
                  goal.FStar_Tactics_Types.context [b]
                 in
              let typ' = comp_to_typ c  in
              let uu____2105 = new_uvar "intro" env' typ'  in
              bind uu____2105
                (fun u  ->
                   let uu____2112 =
                     let uu____2113 =
                       FStar_Syntax_Util.abs [b] u
                         FStar_Pervasives_Native.None
                        in
                     trysolve goal uu____2113  in
                   if uu____2112
                   then
                     let uu____2116 =
                       let uu____2119 =
                         let uu___309_2120 = goal  in
                         let uu____2121 = bnorm env' u  in
                         let uu____2122 = bnorm env' typ'  in
                         {
                           FStar_Tactics_Types.context = env';
                           FStar_Tactics_Types.witness = uu____2121;
                           FStar_Tactics_Types.goal_ty = uu____2122;
                           FStar_Tactics_Types.opts =
                             (uu___309_2120.FStar_Tactics_Types.opts);
                           FStar_Tactics_Types.is_guard =
                             (uu___309_2120.FStar_Tactics_Types.is_guard)
                         }  in
                       replace_cur uu____2119  in
                     bind uu____2116 (fun uu____2124  -> ret b)
                   else fail "intro: unification failed"))
       | FStar_Pervasives_Native.None  ->
           let uu____2130 =
             tts goal.FStar_Tactics_Types.context
               goal.FStar_Tactics_Types.goal_ty
              in
           fail1 "intro: goal is not an arrow (%s)" uu____2130)
  
let intro_rec :
  (FStar_Syntax_Syntax.binder,FStar_Syntax_Syntax.binder)
    FStar_Pervasives_Native.tuple2 tac
  =
  bind cur_goal
    (fun goal  ->
       FStar_Util.print_string
         "WARNING (intro_rec): calling this is known to cause normalizer loops\n";
       FStar_Util.print_string
         "WARNING (intro_rec): proceed at your own risk...\n";
       (let uu____2151 =
          FStar_Syntax_Util.arrow_one goal.FStar_Tactics_Types.goal_ty  in
        match uu____2151 with
        | FStar_Pervasives_Native.Some (b,c) ->
            let uu____2170 =
              let uu____2171 = FStar_Syntax_Util.is_total_comp c  in
              Prims.op_Negation uu____2171  in
            if uu____2170
            then fail "Codomain is effectful"
            else
              (let bv =
                 FStar_Syntax_Syntax.gen_bv "__recf"
                   FStar_Pervasives_Native.None
                   goal.FStar_Tactics_Types.goal_ty
                  in
               let bs =
                 let uu____2187 = FStar_Syntax_Syntax.mk_binder bv  in
                 [uu____2187; b]  in
               let env' =
                 FStar_TypeChecker_Env.push_binders
                   goal.FStar_Tactics_Types.context bs
                  in
               let uu____2189 =
                 let uu____2192 = comp_to_typ c  in
                 new_uvar "intro_rec" env' uu____2192  in
               bind uu____2189
                 (fun u  ->
                    let lb =
                      let uu____2208 =
                        FStar_Syntax_Util.abs [b] u
                          FStar_Pervasives_Native.None
                         in
                      FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl bv) []
                        goal.FStar_Tactics_Types.goal_ty
                        FStar_Parser_Const.effect_Tot_lid uu____2208
                       in
                    let body = FStar_Syntax_Syntax.bv_to_name bv  in
                    let uu____2212 =
                      FStar_Syntax_Subst.close_let_rec [lb] body  in
                    match uu____2212 with
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
                          let uu____2249 =
                            let uu____2252 =
                              let uu___310_2253 = goal  in
                              let uu____2254 = bnorm env' u  in
                              let uu____2255 =
                                let uu____2256 = comp_to_typ c  in
                                bnorm env' uu____2256  in
                              {
                                FStar_Tactics_Types.context = env';
                                FStar_Tactics_Types.witness = uu____2254;
                                FStar_Tactics_Types.goal_ty = uu____2255;
                                FStar_Tactics_Types.opts =
                                  (uu___310_2253.FStar_Tactics_Types.opts);
                                FStar_Tactics_Types.is_guard =
                                  (uu___310_2253.FStar_Tactics_Types.is_guard)
                              }  in
                            replace_cur uu____2252  in
                          bind uu____2249
                            (fun uu____2263  ->
                               let uu____2264 =
                                 let uu____2269 =
                                   FStar_Syntax_Syntax.mk_binder bv  in
                                 (uu____2269, b)  in
                               ret uu____2264)
                        else fail "intro_rec: unification failed"))
        | FStar_Pervasives_Native.None  ->
            let uu____2283 =
              tts goal.FStar_Tactics_Types.context
                goal.FStar_Tactics_Types.goal_ty
               in
            fail1 "intro_rec: goal is not an arrow (%s)" uu____2283))
  
let norm : FStar_Syntax_Embeddings.norm_step Prims.list -> Prims.unit tac =
  fun s  ->
    bind cur_goal
      (fun goal  ->
         let steps =
           let uu____2307 = FStar_TypeChecker_Normalize.tr_norm_steps s  in
           FStar_List.append
             [FStar_TypeChecker_Normalize.Reify;
             FStar_TypeChecker_Normalize.UnfoldTac] uu____2307
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
           (let uu___311_2314 = goal  in
            {
              FStar_Tactics_Types.context =
                (uu___311_2314.FStar_Tactics_Types.context);
              FStar_Tactics_Types.witness = w;
              FStar_Tactics_Types.goal_ty = t;
              FStar_Tactics_Types.opts =
                (uu___311_2314.FStar_Tactics_Types.opts);
              FStar_Tactics_Types.is_guard =
                (uu___311_2314.FStar_Tactics_Types.is_guard)
            }))
  
let norm_term_env :
  env ->
    FStar_Syntax_Embeddings.norm_step Prims.list ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac
  =
  fun e  ->
    fun s  ->
      fun t  ->
        let uu____2332 =
          bind get
            (fun ps  ->
               let uu____2338 = __tc e t  in
               bind uu____2338
                 (fun uu____2360  ->
                    match uu____2360 with
                    | (t1,uu____2370,guard) ->
                        (FStar_TypeChecker_Rel.force_trivial_guard e guard;
                         (let steps =
                            let uu____2376 =
                              FStar_TypeChecker_Normalize.tr_norm_steps s  in
                            FStar_List.append
                              [FStar_TypeChecker_Normalize.Reify;
                              FStar_TypeChecker_Normalize.UnfoldTac]
                              uu____2376
                             in
                          let t2 =
                            normalize steps
                              ps.FStar_Tactics_Types.main_context t1
                             in
                          ret t2))))
           in
        FStar_All.pipe_left (wrap_err "norm_term") uu____2332
  
let refine_intro : Prims.unit tac =
  let uu____2386 =
    bind cur_goal
      (fun g  ->
         let uu____2393 =
           FStar_TypeChecker_Rel.base_and_refinement
             g.FStar_Tactics_Types.context g.FStar_Tactics_Types.goal_ty
            in
         match uu____2393 with
         | (uu____2406,FStar_Pervasives_Native.None ) ->
             fail "not a refinement"
         | (t,FStar_Pervasives_Native.Some (bv,phi)) ->
             let g1 =
               let uu___312_2431 = g  in
               {
                 FStar_Tactics_Types.context =
                   (uu___312_2431.FStar_Tactics_Types.context);
                 FStar_Tactics_Types.witness =
                   (uu___312_2431.FStar_Tactics_Types.witness);
                 FStar_Tactics_Types.goal_ty = t;
                 FStar_Tactics_Types.opts =
                   (uu___312_2431.FStar_Tactics_Types.opts);
                 FStar_Tactics_Types.is_guard =
                   (uu___312_2431.FStar_Tactics_Types.is_guard)
               }  in
             let uu____2432 =
               let uu____2437 =
                 let uu____2442 =
                   let uu____2443 = FStar_Syntax_Syntax.mk_binder bv  in
                   [uu____2443]  in
                 FStar_Syntax_Subst.open_term uu____2442 phi  in
               match uu____2437 with
               | (bvs,phi1) ->
                   let uu____2450 =
                     let uu____2451 = FStar_List.hd bvs  in
                     FStar_Pervasives_Native.fst uu____2451  in
                   (uu____2450, phi1)
                in
             (match uu____2432 with
              | (bv1,phi1) ->
                  let uu____2464 =
                    let uu____2467 =
                      FStar_Syntax_Subst.subst
                        [FStar_Syntax_Syntax.NT
                           (bv1, (g.FStar_Tactics_Types.witness))] phi1
                       in
                    mk_irrelevant_goal "refine_intro refinement"
                      g.FStar_Tactics_Types.context uu____2467
                      g.FStar_Tactics_Types.opts
                     in
                  bind uu____2464
                    (fun g2  ->
                       bind dismiss (fun uu____2471  -> add_goals [g1; g2]))))
     in
  FStar_All.pipe_left (wrap_err "refine_intro") uu____2386 
let __exact_now :
  Prims.bool -> Prims.bool -> FStar_Syntax_Syntax.term -> Prims.unit tac =
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
             let uu____2495 = __tc env t  in
             bind uu____2495
               (fun uu____2515  ->
                  match uu____2515 with
                  | (t1,typ,guard) ->
                      let uu____2527 =
                        if force_guard
                        then
                          must_trivial goal.FStar_Tactics_Types.context guard
                        else
                          add_goal_from_guard "__exact typing"
                            goal.FStar_Tactics_Types.context guard
                            goal.FStar_Tactics_Types.opts
                         in
                      bind uu____2527
                        (fun uu____2534  ->
                           mlog
                             (fun uu____2538  ->
                                let uu____2539 =
                                  tts goal.FStar_Tactics_Types.context typ
                                   in
                                let uu____2540 =
                                  tts goal.FStar_Tactics_Types.context
                                    goal.FStar_Tactics_Types.goal_ty
                                   in
                                FStar_Util.print2
                                  "exact: unifying %s and %s\n" uu____2539
                                  uu____2540)
                             (fun uu____2543  ->
                                let uu____2544 =
                                  do_unify goal.FStar_Tactics_Types.context
                                    typ goal.FStar_Tactics_Types.goal_ty
                                   in
                                if uu____2544
                                then solve goal t1
                                else
                                  (let uu____2548 =
                                     tts goal.FStar_Tactics_Types.context t1
                                      in
                                   let uu____2549 =
                                     tts goal.FStar_Tactics_Types.context typ
                                      in
                                   let uu____2550 =
                                     tts goal.FStar_Tactics_Types.context
                                       goal.FStar_Tactics_Types.goal_ty
                                      in
                                   fail3
                                     "%s : %s does not exactly solve the goal %s"
                                     uu____2548 uu____2549 uu____2550)))))
  
let t_exact :
  Prims.bool -> Prims.bool -> FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun set_expected_typ1  ->
    fun force_guard  ->
      fun tm  ->
        let uu____2564 =
          mlog
            (fun uu____2569  ->
               let uu____2570 = FStar_Syntax_Print.term_to_string tm  in
               FStar_Util.print1 "exact: tm = %s\n" uu____2570)
            (fun uu____2573  ->
               let uu____2574 =
                 let uu____2581 =
                   __exact_now set_expected_typ1 force_guard tm  in
                 trytac' uu____2581  in
               bind uu____2574
                 (fun uu___286_2590  ->
                    match uu___286_2590 with
                    | FStar_Util.Inr r -> ret ()
                    | FStar_Util.Inl e ->
                        let uu____2599 =
                          let uu____2606 =
                            let uu____2609 =
                              norm [FStar_Syntax_Embeddings.Delta]  in
                            bind uu____2609
                              (fun uu____2613  ->
                                 bind refine_intro
                                   (fun uu____2615  ->
                                      __exact_now set_expected_typ1
                                        force_guard tm))
                             in
                          trytac' uu____2606  in
                        bind uu____2599
                          (fun uu___285_2622  ->
                             match uu___285_2622 with
                             | FStar_Util.Inr r -> ret ()
                             | FStar_Util.Inl uu____2630 -> fail e)))
           in
        FStar_All.pipe_left (wrap_err "exact") uu____2564
  
let uvar_free_in_goal :
  FStar_Syntax_Syntax.uvar -> FStar_Tactics_Types.goal -> Prims.bool =
  fun u  ->
    fun g  ->
      if g.FStar_Tactics_Types.is_guard
      then false
      else
        (let free_uvars =
           let uu____2645 =
             let uu____2652 =
               FStar_Syntax_Free.uvars g.FStar_Tactics_Types.goal_ty  in
             FStar_Util.set_elements uu____2652  in
           FStar_List.map FStar_Pervasives_Native.fst uu____2645  in
         FStar_List.existsML (FStar_Syntax_Unionfind.equiv u) free_uvars)
  
let uvar_free :
  FStar_Syntax_Syntax.uvar -> FStar_Tactics_Types.proofstate -> Prims.bool =
  fun u  ->
    fun ps  ->
      FStar_List.existsML (uvar_free_in_goal u) ps.FStar_Tactics_Types.goals
  
let rec mapM : 'a 'b . ('a -> 'b tac) -> 'a Prims.list -> 'b Prims.list tac =
  fun f  ->
    fun l  ->
      match l with
      | [] -> ret []
      | x::xs ->
          let uu____2712 = f x  in
          bind uu____2712
            (fun y  ->
               let uu____2720 = mapM f xs  in
               bind uu____2720 (fun ys  -> ret (y :: ys)))
  
exception NoUnif 
let uu___is_NoUnif : Prims.exn -> Prims.bool =
  fun projectee  ->
    match projectee with | NoUnif  -> true | uu____2738 -> false
  
let rec __apply :
  Prims.bool ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.typ -> Prims.unit tac
  =
  fun uopt  ->
    fun tm  ->
      fun typ  ->
        bind cur_goal
          (fun goal  ->
             let uu____2755 =
               let uu____2760 = t_exact false true tm  in trytac uu____2760
                in
             bind uu____2755
               (fun uu___287_2767  ->
                  match uu___287_2767 with
                  | FStar_Pervasives_Native.Some r -> ret ()
                  | FStar_Pervasives_Native.None  ->
                      let uu____2773 = FStar_Syntax_Util.arrow_one typ  in
                      (match uu____2773 with
                       | FStar_Pervasives_Native.None  ->
                           FStar_Exn.raise NoUnif
                       | FStar_Pervasives_Native.Some ((bv,aq),c) ->
                           mlog
                             (fun uu____2805  ->
                                let uu____2806 =
                                  FStar_Syntax_Print.binder_to_string
                                    (bv, aq)
                                   in
                                FStar_Util.print1
                                  "__apply: pushing binder %s\n" uu____2806)
                             (fun uu____2809  ->
                                let uu____2810 =
                                  let uu____2811 =
                                    FStar_Syntax_Util.is_total_comp c  in
                                  Prims.op_Negation uu____2811  in
                                if uu____2810
                                then fail "apply: not total codomain"
                                else
                                  (let uu____2815 =
                                     new_uvar "apply"
                                       goal.FStar_Tactics_Types.context
                                       bv.FStar_Syntax_Syntax.sort
                                      in
                                   bind uu____2815
                                     (fun u  ->
                                        let tm' =
                                          FStar_Syntax_Syntax.mk_Tm_app tm
                                            [(u, aq)]
                                            FStar_Pervasives_Native.None
                                            (goal.FStar_Tactics_Types.context).FStar_TypeChecker_Env.range
                                           in
                                        let typ' =
                                          let uu____2835 = comp_to_typ c  in
                                          FStar_All.pipe_left
                                            (FStar_Syntax_Subst.subst
                                               [FStar_Syntax_Syntax.NT
                                                  (bv, u)]) uu____2835
                                           in
                                        let uu____2836 =
                                          __apply uopt tm' typ'  in
                                        bind uu____2836
                                          (fun uu____2844  ->
                                             let u1 =
                                               bnorm
                                                 goal.FStar_Tactics_Types.context
                                                 u
                                                in
                                             let uu____2846 =
                                               let uu____2847 =
                                                 let uu____2850 =
                                                   let uu____2851 =
                                                     FStar_Syntax_Util.head_and_args
                                                       u1
                                                      in
                                                   FStar_Pervasives_Native.fst
                                                     uu____2851
                                                    in
                                                 FStar_Syntax_Subst.compress
                                                   uu____2850
                                                  in
                                               uu____2847.FStar_Syntax_Syntax.n
                                                in
                                             match uu____2846 with
                                             | FStar_Syntax_Syntax.Tm_uvar
                                                 (uvar,uu____2879) ->
                                                 bind get
                                                   (fun ps  ->
                                                      let uu____2907 =
                                                        uopt &&
                                                          (uvar_free uvar ps)
                                                         in
                                                      if uu____2907
                                                      then ret ()
                                                      else
                                                        (let uu____2911 =
                                                           let uu____2914 =
                                                             let uu___313_2915
                                                               = goal  in
                                                             let uu____2916 =
                                                               bnorm
                                                                 goal.FStar_Tactics_Types.context
                                                                 u1
                                                                in
                                                             let uu____2917 =
                                                               bnorm
                                                                 goal.FStar_Tactics_Types.context
                                                                 bv.FStar_Syntax_Syntax.sort
                                                                in
                                                             {
                                                               FStar_Tactics_Types.context
                                                                 =
                                                                 (uu___313_2915.FStar_Tactics_Types.context);
                                                               FStar_Tactics_Types.witness
                                                                 = uu____2916;
                                                               FStar_Tactics_Types.goal_ty
                                                                 = uu____2917;
                                                               FStar_Tactics_Types.opts
                                                                 =
                                                                 (uu___313_2915.FStar_Tactics_Types.opts);
                                                               FStar_Tactics_Types.is_guard
                                                                 = false
                                                             }  in
                                                           [uu____2914]  in
                                                         add_goals uu____2911))
                                             | t -> ret ())))))))
  
let try_unif : 'a . 'a tac -> 'a tac -> 'a tac =
  fun t  ->
    fun t'  -> mk_tac (fun ps  -> try run t ps with | NoUnif  -> run t' ps)
  
let apply : Prims.bool -> FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun uopt  ->
    fun tm  ->
      let uu____2963 =
        mlog
          (fun uu____2968  ->
             let uu____2969 = FStar_Syntax_Print.term_to_string tm  in
             FStar_Util.print1 "apply: tm = %s\n" uu____2969)
          (fun uu____2971  ->
             bind cur_goal
               (fun goal  ->
                  let uu____2975 = __tc goal.FStar_Tactics_Types.context tm
                     in
                  bind uu____2975
                    (fun uu____2996  ->
                       match uu____2996 with
                       | (tm1,typ,guard) ->
                           let uu____3008 =
                             let uu____3011 =
                               let uu____3014 = __apply uopt tm1 typ  in
                               bind uu____3014
                                 (fun uu____3018  ->
                                    add_goal_from_guard "apply guard"
                                      goal.FStar_Tactics_Types.context guard
                                      goal.FStar_Tactics_Types.opts)
                                in
                             focus uu____3011  in
                           let uu____3019 =
                             let uu____3022 =
                               tts goal.FStar_Tactics_Types.context tm1  in
                             let uu____3023 =
                               tts goal.FStar_Tactics_Types.context typ  in
                             let uu____3024 =
                               tts goal.FStar_Tactics_Types.context
                                 goal.FStar_Tactics_Types.goal_ty
                                in
                             fail3
                               "Cannot instantiate %s (of type %s) to match goal (%s)"
                               uu____3022 uu____3023 uu____3024
                              in
                           try_unif uu____3008 uu____3019)))
         in
      FStar_All.pipe_left (wrap_err "apply") uu____2963
  
let apply_lemma : FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun tm  ->
    let uu____3036 =
      let uu____3039 =
        mlog
          (fun uu____3044  ->
             let uu____3045 = FStar_Syntax_Print.term_to_string tm  in
             FStar_Util.print1 "apply_lemma: tm = %s\n" uu____3045)
          (fun uu____3048  ->
             let is_unit_t t =
               let uu____3053 =
                 let uu____3054 = FStar_Syntax_Subst.compress t  in
                 uu____3054.FStar_Syntax_Syntax.n  in
               match uu____3053 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.unit_lid
                   -> true
               | uu____3058 -> false  in
             bind cur_goal
               (fun goal  ->
                  let uu____3062 = __tc goal.FStar_Tactics_Types.context tm
                     in
                  bind uu____3062
                    (fun uu____3084  ->
                       match uu____3084 with
                       | (tm1,t,guard) ->
                           let uu____3096 =
                             FStar_Syntax_Util.arrow_formals_comp t  in
                           (match uu____3096 with
                            | (bs,comp) ->
                                if
                                  Prims.op_Negation
                                    (FStar_Syntax_Util.is_lemma_comp comp)
                                then fail "not a lemma"
                                else
                                  (let uu____3126 =
                                     FStar_List.fold_left
                                       (fun uu____3172  ->
                                          fun uu____3173  ->
                                            match (uu____3172, uu____3173)
                                            with
                                            | ((uvs,guard1,subst1),(b,aq)) ->
                                                let b_t =
                                                  FStar_Syntax_Subst.subst
                                                    subst1
                                                    b.FStar_Syntax_Syntax.sort
                                                   in
                                                let uu____3276 =
                                                  is_unit_t b_t  in
                                                if uu____3276
                                                then
                                                  (((FStar_Syntax_Util.exp_unit,
                                                      aq) :: uvs), guard1,
                                                    ((FStar_Syntax_Syntax.NT
                                                        (b,
                                                          FStar_Syntax_Util.exp_unit))
                                                    :: subst1))
                                                else
                                                  (let uu____3314 =
                                                     FStar_TypeChecker_Util.new_implicit_var
                                                       "apply_lemma"
                                                       (goal.FStar_Tactics_Types.goal_ty).FStar_Syntax_Syntax.pos
                                                       goal.FStar_Tactics_Types.context
                                                       b_t
                                                      in
                                                   match uu____3314 with
                                                   | (u,uu____3344,g_u) ->
                                                       let uu____3358 =
                                                         FStar_TypeChecker_Rel.conj_guard
                                                           guard1 g_u
                                                          in
                                                       (((u, aq) :: uvs),
                                                         uu____3358,
                                                         ((FStar_Syntax_Syntax.NT
                                                             (b, u)) ::
                                                         subst1))))
                                       ([], guard, []) bs
                                      in
                                   match uu____3126 with
                                   | (uvs,implicits,subst1) ->
                                       let uvs1 = FStar_List.rev uvs  in
                                       let comp1 =
                                         FStar_Syntax_Subst.subst_comp subst1
                                           comp
                                          in
                                       let uu____3428 =
                                         let uu____3437 =
                                           let uu____3446 =
                                             FStar_Syntax_Util.comp_to_comp_typ
                                               comp1
                                              in
                                           uu____3446.FStar_Syntax_Syntax.effect_args
                                            in
                                         match uu____3437 with
                                         | pre::post::uu____3457 ->
                                             ((FStar_Pervasives_Native.fst
                                                 pre),
                                               (FStar_Pervasives_Native.fst
                                                  post))
                                         | uu____3498 ->
                                             failwith
                                               "apply_lemma: impossible: not a lemma"
                                          in
                                       (match uu____3428 with
                                        | (pre,post) ->
                                            let post1 =
                                              let uu____3530 =
                                                let uu____3539 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    FStar_Syntax_Util.exp_unit
                                                   in
                                                [uu____3539]  in
                                              FStar_Syntax_Util.mk_app post
                                                uu____3530
                                               in
                                            let uu____3540 =
                                              let uu____3541 =
                                                let uu____3542 =
                                                  FStar_Syntax_Util.mk_squash
                                                    FStar_Syntax_Syntax.U_zero
                                                    post1
                                                   in
                                                do_unify
                                                  goal.FStar_Tactics_Types.context
                                                  uu____3542
                                                  goal.FStar_Tactics_Types.goal_ty
                                                 in
                                              Prims.op_Negation uu____3541
                                               in
                                            if uu____3540
                                            then
                                              let uu____3545 =
                                                tts
                                                  goal.FStar_Tactics_Types.context
                                                  tm1
                                                 in
                                              let uu____3546 =
                                                let uu____3547 =
                                                  FStar_Syntax_Util.mk_squash
                                                    FStar_Syntax_Syntax.U_zero
                                                    post1
                                                   in
                                                tts
                                                  goal.FStar_Tactics_Types.context
                                                  uu____3547
                                                 in
                                              let uu____3548 =
                                                tts
                                                  goal.FStar_Tactics_Types.context
                                                  goal.FStar_Tactics_Types.goal_ty
                                                 in
                                              fail3
                                                "Cannot instantiate lemma %s (with postcondition: %s) to match goal (%s)"
                                                uu____3545 uu____3546
                                                uu____3548
                                            else
                                              (let solution =
                                                 let uu____3551 =
                                                   FStar_Syntax_Syntax.mk_Tm_app
                                                     tm1 uvs1
                                                     FStar_Pervasives_Native.None
                                                     (goal.FStar_Tactics_Types.context).FStar_TypeChecker_Env.range
                                                    in
                                                 FStar_TypeChecker_Normalize.normalize
                                                   [FStar_TypeChecker_Normalize.Beta]
                                                   goal.FStar_Tactics_Types.context
                                                   uu____3551
                                                  in
                                               let uu____3552 =
                                                 add_implicits
                                                   implicits.FStar_TypeChecker_Env.implicits
                                                  in
                                               bind uu____3552
                                                 (fun uu____3557  ->
                                                    let uu____3558 =
                                                      solve goal
                                                        FStar_Syntax_Util.exp_unit
                                                       in
                                                    bind uu____3558
                                                      (fun uu____3566  ->
                                                         let is_free_uvar uv
                                                           t1 =
                                                           let free_uvars =
                                                             let uu____3577 =
                                                               let uu____3584
                                                                 =
                                                                 FStar_Syntax_Free.uvars
                                                                   t1
                                                                  in
                                                               FStar_Util.set_elements
                                                                 uu____3584
                                                                in
                                                             FStar_List.map
                                                               FStar_Pervasives_Native.fst
                                                               uu____3577
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
                                                           let uu____3625 =
                                                             FStar_Syntax_Util.head_and_args
                                                               t1
                                                              in
                                                           match uu____3625
                                                           with
                                                           | (hd1,uu____3641)
                                                               ->
                                                               (match 
                                                                  hd1.FStar_Syntax_Syntax.n
                                                                with
                                                                | FStar_Syntax_Syntax.Tm_uvar
                                                                    (uv,uu____3663)
                                                                    ->
                                                                    appears
                                                                    uv goals
                                                                | uu____3688
                                                                    -> false)
                                                            in
                                                         let uu____3689 =
                                                           FStar_All.pipe_right
                                                             implicits.FStar_TypeChecker_Env.implicits
                                                             (mapM
                                                                (fun
                                                                   uu____3761
                                                                    ->
                                                                   match uu____3761
                                                                   with
                                                                   | 
                                                                   (_msg,env,_uvar,term,typ,uu____3789)
                                                                    ->
                                                                    let uu____3790
                                                                    =
                                                                    FStar_Syntax_Util.head_and_args
                                                                    term  in
                                                                    (match uu____3790
                                                                    with
                                                                    | 
                                                                    (hd1,uu____3816)
                                                                    ->
                                                                    let uu____3837
                                                                    =
                                                                    let uu____3838
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    hd1  in
                                                                    uu____3838.FStar_Syntax_Syntax.n
                                                                     in
                                                                    (match uu____3837
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Tm_uvar
                                                                    uu____3851
                                                                    ->
                                                                    let uu____3868
                                                                    =
                                                                    let uu____3877
                                                                    =
                                                                    let uu____3880
                                                                    =
                                                                    let uu___316_3881
                                                                    = goal
                                                                     in
                                                                    let uu____3882
                                                                    =
                                                                    bnorm
                                                                    goal.FStar_Tactics_Types.context
                                                                    term  in
                                                                    let uu____3883
                                                                    =
                                                                    bnorm
                                                                    goal.FStar_Tactics_Types.context
                                                                    typ  in
                                                                    {
                                                                    FStar_Tactics_Types.context
                                                                    =
                                                                    (uu___316_3881.FStar_Tactics_Types.context);
                                                                    FStar_Tactics_Types.witness
                                                                    =
                                                                    uu____3882;
                                                                    FStar_Tactics_Types.goal_ty
                                                                    =
                                                                    uu____3883;
                                                                    FStar_Tactics_Types.opts
                                                                    =
                                                                    (uu___316_3881.FStar_Tactics_Types.opts);
                                                                    FStar_Tactics_Types.is_guard
                                                                    =
                                                                    (uu___316_3881.FStar_Tactics_Types.is_guard)
                                                                    }  in
                                                                    [uu____3880]
                                                                     in
                                                                    (uu____3877,
                                                                    [])  in
                                                                    ret
                                                                    uu____3868
                                                                    | 
                                                                    uu____3896
                                                                    ->
                                                                    let term1
                                                                    =
                                                                    bnorm env
                                                                    term  in
                                                                    let uu____3898
                                                                    =
                                                                    let uu____3905
                                                                    =
                                                                    FStar_TypeChecker_Env.set_expected_typ
                                                                    env typ
                                                                     in
                                                                    env.FStar_TypeChecker_Env.type_of
                                                                    uu____3905
                                                                    term1  in
                                                                    (match uu____3898
                                                                    with
                                                                    | 
                                                                    (uu____3916,uu____3917,g_typ)
                                                                    ->
                                                                    let uu____3919
                                                                    =
                                                                    goal_from_guard
                                                                    "apply_lemma solved arg"
                                                                    goal.FStar_Tactics_Types.context
                                                                    g_typ
                                                                    goal.FStar_Tactics_Types.opts
                                                                     in
                                                                    bind
                                                                    uu____3919
                                                                    (fun
                                                                    uu___288_3935
                                                                     ->
                                                                    match uu___288_3935
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
                                                         bind uu____3689
                                                           (fun goals_  ->
                                                              let sub_goals =
                                                                let uu____4003
                                                                  =
                                                                  FStar_List.map
                                                                    FStar_Pervasives_Native.fst
                                                                    goals_
                                                                   in
                                                                FStar_List.flatten
                                                                  uu____4003
                                                                 in
                                                              let smt_goals =
                                                                let uu____4025
                                                                  =
                                                                  FStar_List.map
                                                                    FStar_Pervasives_Native.snd
                                                                    goals_
                                                                   in
                                                                FStar_List.flatten
                                                                  uu____4025
                                                                 in
                                                              let rec filter'
                                                                f xs =
                                                                match xs with
                                                                | [] -> []
                                                                | x::xs1 ->
                                                                    let uu____4081
                                                                    = f x xs1
                                                                     in
                                                                    if
                                                                    uu____4081
                                                                    then
                                                                    let uu____4084
                                                                    =
                                                                    filter' f
                                                                    xs1  in x
                                                                    ::
                                                                    uu____4084
                                                                    else
                                                                    filter' f
                                                                    xs1
                                                                 in
                                                              let sub_goals1
                                                                =
                                                                filter'
                                                                  (fun g  ->
                                                                    fun goals
                                                                     ->
                                                                    let uu____4098
                                                                    =
                                                                    checkone
                                                                    g.FStar_Tactics_Types.witness
                                                                    goals  in
                                                                    Prims.op_Negation
                                                                    uu____4098)
                                                                  sub_goals
                                                                 in
                                                              let uu____4099
                                                                =
                                                                add_goal_from_guard
                                                                  "apply_lemma guard"
                                                                  goal.FStar_Tactics_Types.context
                                                                  guard
                                                                  goal.FStar_Tactics_Types.opts
                                                                 in
                                                              bind uu____4099
                                                                (fun
                                                                   uu____4104
                                                                    ->
                                                                   let uu____4105
                                                                    =
                                                                    let uu____4108
                                                                    =
                                                                    let uu____4109
                                                                    =
                                                                    let uu____4110
                                                                    =
                                                                    FStar_Syntax_Util.mk_squash
                                                                    FStar_Syntax_Syntax.U_zero
                                                                    pre  in
                                                                    istrivial
                                                                    goal.FStar_Tactics_Types.context
                                                                    uu____4110
                                                                     in
                                                                    Prims.op_Negation
                                                                    uu____4109
                                                                     in
                                                                    if
                                                                    uu____4108
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
                                                                    uu____4105
                                                                    (fun
                                                                    uu____4116
                                                                     ->
                                                                    let uu____4117
                                                                    =
                                                                    add_smt_goals
                                                                    smt_goals
                                                                     in
                                                                    bind
                                                                    uu____4117
                                                                    (fun
                                                                    uu____4121
                                                                     ->
                                                                    add_goals
                                                                    sub_goals1)))))))))))))
         in
      focus uu____3039  in
    FStar_All.pipe_left (wrap_err "apply_lemma") uu____3036
  
let destruct_eq' :
  FStar_Syntax_Syntax.typ ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun typ  ->
    let uu____4141 = FStar_Syntax_Util.destruct_typ_as_formula typ  in
    match uu____4141 with
    | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn
        (l,uu____4151::(e1,uu____4153)::(e2,uu____4155)::[])) when
        FStar_Ident.lid_equals l FStar_Parser_Const.eq2_lid ->
        FStar_Pervasives_Native.Some (e1, e2)
    | uu____4214 -> FStar_Pervasives_Native.None
  
let destruct_eq :
  FStar_Syntax_Syntax.typ ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun typ  ->
    let uu____4236 = destruct_eq' typ  in
    match uu____4236 with
    | FStar_Pervasives_Native.Some t -> FStar_Pervasives_Native.Some t
    | FStar_Pervasives_Native.None  ->
        let uu____4266 = FStar_Syntax_Util.un_squash typ  in
        (match uu____4266 with
         | FStar_Pervasives_Native.Some typ1 -> destruct_eq' typ1
         | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None)
  
let split_env :
  FStar_Syntax_Syntax.bv ->
    env ->
      (env,FStar_Syntax_Syntax.bv Prims.list) FStar_Pervasives_Native.tuple2
        FStar_Pervasives_Native.option
  =
  fun bvar  ->
    fun e  ->
      let rec aux e1 =
        let uu____4322 = FStar_TypeChecker_Env.pop_bv e1  in
        match uu____4322 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (bv',e') ->
            if FStar_Syntax_Syntax.bv_eq bvar bv'
            then FStar_Pervasives_Native.Some (e', [])
            else
              (let uu____4370 = aux e'  in
               FStar_Util.map_opt uu____4370
                 (fun uu____4394  ->
                    match uu____4394 with | (e'',bvs) -> (e'', (bv' :: bvs))))
         in
      let uu____4415 = aux e  in
      FStar_Util.map_opt uu____4415
        (fun uu____4439  ->
           match uu____4439 with | (e',bvs) -> (e', (FStar_List.rev bvs)))
  
let push_bvs :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.bv Prims.list -> FStar_TypeChecker_Env.env
  =
  fun e  ->
    fun bvs  ->
      FStar_List.fold_left
        (fun e1  -> fun b  -> FStar_TypeChecker_Env.push_bv e1 b) e bvs
  
let subst_goal :
  FStar_Syntax_Syntax.bv ->
    FStar_Syntax_Syntax.bv ->
      FStar_Syntax_Syntax.subst_elt Prims.list ->
        FStar_Tactics_Types.goal ->
          FStar_Tactics_Types.goal FStar_Pervasives_Native.option
  =
  fun b1  ->
    fun b2  ->
      fun s  ->
        fun g  ->
          let uu____4494 = split_env b1 g.FStar_Tactics_Types.context  in
          FStar_Util.map_opt uu____4494
            (fun uu____4518  ->
               match uu____4518 with
               | (e0,bvs) ->
                   let s1 bv =
                     let uu___317_4535 = bv  in
                     let uu____4536 =
                       FStar_Syntax_Subst.subst s bv.FStar_Syntax_Syntax.sort
                        in
                     {
                       FStar_Syntax_Syntax.ppname =
                         (uu___317_4535.FStar_Syntax_Syntax.ppname);
                       FStar_Syntax_Syntax.index =
                         (uu___317_4535.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort = uu____4536
                     }  in
                   let bvs1 = FStar_List.map s1 bvs  in
                   let c = push_bvs e0 (b2 :: bvs1)  in
                   let w =
                     FStar_Syntax_Subst.subst s g.FStar_Tactics_Types.witness
                      in
                   let t =
                     FStar_Syntax_Subst.subst s g.FStar_Tactics_Types.goal_ty
                      in
                   let uu___318_4545 = g  in
                   {
                     FStar_Tactics_Types.context = c;
                     FStar_Tactics_Types.witness = w;
                     FStar_Tactics_Types.goal_ty = t;
                     FStar_Tactics_Types.opts =
                       (uu___318_4545.FStar_Tactics_Types.opts);
                     FStar_Tactics_Types.is_guard =
                       (uu___318_4545.FStar_Tactics_Types.is_guard)
                   })
  
let rewrite : FStar_Syntax_Syntax.binder -> Prims.unit tac =
  fun h  ->
    bind cur_goal
      (fun goal  ->
         let uu____4558 = h  in
         match uu____4558 with
         | (bv,uu____4562) ->
             mlog
               (fun uu____4566  ->
                  let uu____4567 = FStar_Syntax_Print.bv_to_string bv  in
                  let uu____4568 =
                    tts goal.FStar_Tactics_Types.context
                      bv.FStar_Syntax_Syntax.sort
                     in
                  FStar_Util.print2 "+++Rewrite %s : %s\n" uu____4567
                    uu____4568)
               (fun uu____4571  ->
                  let uu____4572 =
                    split_env bv goal.FStar_Tactics_Types.context  in
                  match uu____4572 with
                  | FStar_Pervasives_Native.None  ->
                      fail "rewrite: binder not found in environment"
                  | FStar_Pervasives_Native.Some (e0,bvs) ->
                      let uu____4601 =
                        destruct_eq bv.FStar_Syntax_Syntax.sort  in
                      (match uu____4601 with
                       | FStar_Pervasives_Native.Some (x,e) ->
                           let uu____4616 =
                             let uu____4617 = FStar_Syntax_Subst.compress x
                                in
                             uu____4617.FStar_Syntax_Syntax.n  in
                           (match uu____4616 with
                            | FStar_Syntax_Syntax.Tm_name x1 ->
                                let s = [FStar_Syntax_Syntax.NT (x1, e)]  in
                                let s1 bv1 =
                                  let uu___319_4630 = bv1  in
                                  let uu____4631 =
                                    FStar_Syntax_Subst.subst s
                                      bv1.FStar_Syntax_Syntax.sort
                                     in
                                  {
                                    FStar_Syntax_Syntax.ppname =
                                      (uu___319_4630.FStar_Syntax_Syntax.ppname);
                                    FStar_Syntax_Syntax.index =
                                      (uu___319_4630.FStar_Syntax_Syntax.index);
                                    FStar_Syntax_Syntax.sort = uu____4631
                                  }  in
                                let bvs1 = FStar_List.map s1 bvs  in
                                let uu____4637 =
                                  let uu___320_4638 = goal  in
                                  let uu____4639 = push_bvs e0 (bv :: bvs1)
                                     in
                                  let uu____4640 =
                                    FStar_Syntax_Subst.subst s
                                      goal.FStar_Tactics_Types.witness
                                     in
                                  let uu____4641 =
                                    FStar_Syntax_Subst.subst s
                                      goal.FStar_Tactics_Types.goal_ty
                                     in
                                  {
                                    FStar_Tactics_Types.context = uu____4639;
                                    FStar_Tactics_Types.witness = uu____4640;
                                    FStar_Tactics_Types.goal_ty = uu____4641;
                                    FStar_Tactics_Types.opts =
                                      (uu___320_4638.FStar_Tactics_Types.opts);
                                    FStar_Tactics_Types.is_guard =
                                      (uu___320_4638.FStar_Tactics_Types.is_guard)
                                  }  in
                                replace_cur uu____4637
                            | uu____4642 ->
                                fail
                                  "rewrite: Not an equality hypothesis with a variable on the LHS")
                       | uu____4643 ->
                           fail "rewrite: Not an equality hypothesis")))
  
let rename_to : FStar_Syntax_Syntax.binder -> Prims.string -> Prims.unit tac
  =
  fun b  ->
    fun s  ->
      bind cur_goal
        (fun goal  ->
           let uu____4668 = b  in
           match uu____4668 with
           | (bv,uu____4672) ->
               let bv' =
                 FStar_Syntax_Syntax.freshen_bv
                   (let uu___321_4676 = bv  in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (FStar_Ident.mk_ident
                           (s,
                             ((bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange)));
                      FStar_Syntax_Syntax.index =
                        (uu___321_4676.FStar_Syntax_Syntax.index);
                      FStar_Syntax_Syntax.sort =
                        (uu___321_4676.FStar_Syntax_Syntax.sort)
                    })
                  in
               let s1 =
                 let uu____4680 =
                   let uu____4681 =
                     let uu____4688 = FStar_Syntax_Syntax.bv_to_name bv'  in
                     (bv, uu____4688)  in
                   FStar_Syntax_Syntax.NT uu____4681  in
                 [uu____4680]  in
               let uu____4689 = subst_goal bv bv' s1 goal  in
               (match uu____4689 with
                | FStar_Pervasives_Native.None  ->
                    fail "rename_to: binder not found in environment"
                | FStar_Pervasives_Native.Some goal1 -> replace_cur goal1))
  
let binder_retype : FStar_Syntax_Syntax.binder -> Prims.unit tac =
  fun b  ->
    bind cur_goal
      (fun goal  ->
         let uu____4708 = b  in
         match uu____4708 with
         | (bv,uu____4712) ->
             let uu____4713 = split_env bv goal.FStar_Tactics_Types.context
                in
             (match uu____4713 with
              | FStar_Pervasives_Native.None  ->
                  fail "binder_retype: binder is not present in environment"
              | FStar_Pervasives_Native.Some (e0,bvs) ->
                  let uu____4742 = FStar_Syntax_Util.type_u ()  in
                  (match uu____4742 with
                   | (ty,u) ->
                       let uu____4751 = new_uvar "binder_retype" e0 ty  in
                       bind uu____4751
                         (fun t'  ->
                            let bv'' =
                              let uu___322_4761 = bv  in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___322_4761.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___322_4761.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = t'
                              }  in
                            let s =
                              let uu____4765 =
                                let uu____4766 =
                                  let uu____4773 =
                                    FStar_Syntax_Syntax.bv_to_name bv''  in
                                  (bv, uu____4773)  in
                                FStar_Syntax_Syntax.NT uu____4766  in
                              [uu____4765]  in
                            let bvs1 =
                              FStar_List.map
                                (fun b1  ->
                                   let uu___323_4781 = b1  in
                                   let uu____4782 =
                                     FStar_Syntax_Subst.subst s
                                       b1.FStar_Syntax_Syntax.sort
                                      in
                                   {
                                     FStar_Syntax_Syntax.ppname =
                                       (uu___323_4781.FStar_Syntax_Syntax.ppname);
                                     FStar_Syntax_Syntax.index =
                                       (uu___323_4781.FStar_Syntax_Syntax.index);
                                     FStar_Syntax_Syntax.sort = uu____4782
                                   }) bvs
                               in
                            let env' = push_bvs e0 (bv'' :: bvs1)  in
                            bind dismiss
                              (fun uu____4788  ->
                                 let uu____4789 =
                                   let uu____4792 =
                                     let uu____4795 =
                                       let uu___324_4796 = goal  in
                                       let uu____4797 =
                                         FStar_Syntax_Subst.subst s
                                           goal.FStar_Tactics_Types.witness
                                          in
                                       let uu____4798 =
                                         FStar_Syntax_Subst.subst s
                                           goal.FStar_Tactics_Types.goal_ty
                                          in
                                       {
                                         FStar_Tactics_Types.context = env';
                                         FStar_Tactics_Types.witness =
                                           uu____4797;
                                         FStar_Tactics_Types.goal_ty =
                                           uu____4798;
                                         FStar_Tactics_Types.opts =
                                           (uu___324_4796.FStar_Tactics_Types.opts);
                                         FStar_Tactics_Types.is_guard =
                                           (uu___324_4796.FStar_Tactics_Types.is_guard)
                                       }  in
                                     [uu____4795]  in
                                   add_goals uu____4792  in
                                 bind uu____4789
                                   (fun uu____4801  ->
                                      let uu____4802 =
                                        FStar_Syntax_Util.mk_eq2
                                          (FStar_Syntax_Syntax.U_succ u) ty
                                          bv.FStar_Syntax_Syntax.sort t'
                                         in
                                      add_irrelevant_goal
                                        "binder_retype equation" e0
                                        uu____4802
                                        goal.FStar_Tactics_Types.opts))))))
  
let norm_binder_type :
  FStar_Syntax_Embeddings.norm_step Prims.list ->
    FStar_Syntax_Syntax.binder -> Prims.unit tac
  =
  fun s  ->
    fun b  ->
      bind cur_goal
        (fun goal  ->
           let uu____4823 = b  in
           match uu____4823 with
           | (bv,uu____4827) ->
               let uu____4828 = split_env bv goal.FStar_Tactics_Types.context
                  in
               (match uu____4828 with
                | FStar_Pervasives_Native.None  ->
                    fail
                      "binder_retype: binder is not present in environment"
                | FStar_Pervasives_Native.Some (e0,bvs) ->
                    let steps =
                      let uu____4860 =
                        FStar_TypeChecker_Normalize.tr_norm_steps s  in
                      FStar_List.append
                        [FStar_TypeChecker_Normalize.Reify;
                        FStar_TypeChecker_Normalize.UnfoldTac] uu____4860
                       in
                    let sort' =
                      normalize steps e0 bv.FStar_Syntax_Syntax.sort  in
                    let bv' =
                      let uu___325_4865 = bv  in
                      {
                        FStar_Syntax_Syntax.ppname =
                          (uu___325_4865.FStar_Syntax_Syntax.ppname);
                        FStar_Syntax_Syntax.index =
                          (uu___325_4865.FStar_Syntax_Syntax.index);
                        FStar_Syntax_Syntax.sort = sort'
                      }  in
                    let env' = push_bvs e0 (bv' :: bvs)  in
                    replace_cur
                      (let uu___326_4869 = goal  in
                       {
                         FStar_Tactics_Types.context = env';
                         FStar_Tactics_Types.witness =
                           (uu___326_4869.FStar_Tactics_Types.witness);
                         FStar_Tactics_Types.goal_ty =
                           (uu___326_4869.FStar_Tactics_Types.goal_ty);
                         FStar_Tactics_Types.opts =
                           (uu___326_4869.FStar_Tactics_Types.opts);
                         FStar_Tactics_Types.is_guard =
                           (uu___326_4869.FStar_Tactics_Types.is_guard)
                       })))
  
let revert : Prims.unit tac =
  bind cur_goal
    (fun goal  ->
       let uu____4875 =
         FStar_TypeChecker_Env.pop_bv goal.FStar_Tactics_Types.context  in
       match uu____4875 with
       | FStar_Pervasives_Native.None  -> fail "Cannot revert; empty context"
       | FStar_Pervasives_Native.Some (x,env') ->
           let typ' =
             let uu____4897 =
               FStar_Syntax_Syntax.mk_Total goal.FStar_Tactics_Types.goal_ty
                in
             FStar_Syntax_Util.arrow [(x, FStar_Pervasives_Native.None)]
               uu____4897
              in
           let w' =
             FStar_Syntax_Util.abs [(x, FStar_Pervasives_Native.None)]
               goal.FStar_Tactics_Types.witness FStar_Pervasives_Native.None
              in
           replace_cur
             (let uu___327_4931 = goal  in
              {
                FStar_Tactics_Types.context = env';
                FStar_Tactics_Types.witness = w';
                FStar_Tactics_Types.goal_ty = typ';
                FStar_Tactics_Types.opts =
                  (uu___327_4931.FStar_Tactics_Types.opts);
                FStar_Tactics_Types.is_guard =
                  (uu___327_4931.FStar_Tactics_Types.is_guard)
              }))
  
let revert_hd : name -> Prims.unit tac =
  fun x  ->
    bind cur_goal
      (fun goal  ->
         let uu____4942 =
           FStar_TypeChecker_Env.pop_bv goal.FStar_Tactics_Types.context  in
         match uu____4942 with
         | FStar_Pervasives_Native.None  ->
             fail "Cannot revert_hd; empty context"
         | FStar_Pervasives_Native.Some (y,env') ->
             if Prims.op_Negation (FStar_Syntax_Syntax.bv_eq x y)
             then
               let uu____4963 = FStar_Syntax_Print.bv_to_string x  in
               let uu____4964 = FStar_Syntax_Print.bv_to_string y  in
               fail2
                 "Cannot revert_hd %s; head variable mismatch ... egot %s"
                 uu____4963 uu____4964
             else revert)
  
let clear_top : Prims.unit tac =
  bind cur_goal
    (fun goal  ->
       let uu____4971 =
         FStar_TypeChecker_Env.pop_bv goal.FStar_Tactics_Types.context  in
       match uu____4971 with
       | FStar_Pervasives_Native.None  -> fail "Cannot clear; empty context"
       | FStar_Pervasives_Native.Some (x,env') ->
           let fns_ty =
             FStar_Syntax_Free.names goal.FStar_Tactics_Types.goal_ty  in
           let uu____4993 = FStar_Util.set_mem x fns_ty  in
           if uu____4993
           then fail "Cannot clear; variable appears in goal"
           else
             (let uu____4997 =
                new_uvar "clear_top" env' goal.FStar_Tactics_Types.goal_ty
                 in
              bind uu____4997
                (fun u  ->
                   let uu____5003 =
                     let uu____5004 = trysolve goal u  in
                     Prims.op_Negation uu____5004  in
                   if uu____5003
                   then fail "clear: unification failed"
                   else
                     (let new_goal =
                        let uu___328_5009 = goal  in
                        let uu____5010 = bnorm env' u  in
                        {
                          FStar_Tactics_Types.context = env';
                          FStar_Tactics_Types.witness = uu____5010;
                          FStar_Tactics_Types.goal_ty =
                            (uu___328_5009.FStar_Tactics_Types.goal_ty);
                          FStar_Tactics_Types.opts =
                            (uu___328_5009.FStar_Tactics_Types.opts);
                          FStar_Tactics_Types.is_guard =
                            (uu___328_5009.FStar_Tactics_Types.is_guard)
                        }  in
                      bind dismiss (fun uu____5012  -> add_goals [new_goal])))))
  
let rec clear : FStar_Syntax_Syntax.binder -> Prims.unit tac =
  fun b  ->
    bind cur_goal
      (fun goal  ->
         let uu____5023 =
           FStar_TypeChecker_Env.pop_bv goal.FStar_Tactics_Types.context  in
         match uu____5023 with
         | FStar_Pervasives_Native.None  ->
             fail "Cannot clear; empty context"
         | FStar_Pervasives_Native.Some (b',env') ->
             if FStar_Syntax_Syntax.bv_eq (FStar_Pervasives_Native.fst b) b'
             then clear_top
             else
               bind revert
                 (fun uu____5047  ->
                    let uu____5048 = clear b  in
                    bind uu____5048
                      (fun uu____5052  ->
                         bind intro (fun uu____5054  -> ret ()))))
  
let prune : Prims.string -> Prims.unit tac =
  fun s  ->
    bind cur_goal
      (fun g  ->
         let ctx = g.FStar_Tactics_Types.context  in
         let ctx' =
           FStar_TypeChecker_Env.rem_proof_ns ctx
             (FStar_Ident.path_of_text s)
            in
         let g' =
           let uu___329_5070 = g  in
           {
             FStar_Tactics_Types.context = ctx';
             FStar_Tactics_Types.witness =
               (uu___329_5070.FStar_Tactics_Types.witness);
             FStar_Tactics_Types.goal_ty =
               (uu___329_5070.FStar_Tactics_Types.goal_ty);
             FStar_Tactics_Types.opts =
               (uu___329_5070.FStar_Tactics_Types.opts);
             FStar_Tactics_Types.is_guard =
               (uu___329_5070.FStar_Tactics_Types.is_guard)
           }  in
         bind dismiss (fun uu____5072  -> add_goals [g']))
  
let addns : Prims.string -> Prims.unit tac =
  fun s  ->
    bind cur_goal
      (fun g  ->
         let ctx = g.FStar_Tactics_Types.context  in
         let ctx' =
           FStar_TypeChecker_Env.add_proof_ns ctx
             (FStar_Ident.path_of_text s)
            in
         let g' =
           let uu___330_5088 = g  in
           {
             FStar_Tactics_Types.context = ctx';
             FStar_Tactics_Types.witness =
               (uu___330_5088.FStar_Tactics_Types.witness);
             FStar_Tactics_Types.goal_ty =
               (uu___330_5088.FStar_Tactics_Types.goal_ty);
             FStar_Tactics_Types.opts =
               (uu___330_5088.FStar_Tactics_Types.opts);
             FStar_Tactics_Types.is_guard =
               (uu___330_5088.FStar_Tactics_Types.is_guard)
           }  in
         bind dismiss (fun uu____5090  -> add_goals [g']))
  
let rec tac_fold_env :
  FStar_Tactics_Types.direction ->
    (env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac) ->
      env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac
  =
  fun d  ->
    fun f  ->
      fun env  ->
        fun t  ->
          let tn =
            let uu____5122 = FStar_Syntax_Subst.compress t  in
            uu____5122.FStar_Syntax_Syntax.n  in
          let uu____5125 =
            if d = FStar_Tactics_Types.TopDown
            then
              f env
                (let uu___332_5131 = t  in
                 {
                   FStar_Syntax_Syntax.n = tn;
                   FStar_Syntax_Syntax.pos =
                     (uu___332_5131.FStar_Syntax_Syntax.pos);
                   FStar_Syntax_Syntax.vars =
                     (uu___332_5131.FStar_Syntax_Syntax.vars)
                 })
            else ret t  in
          bind uu____5125
            (fun t1  ->
               let tn1 =
                 let uu____5139 =
                   let uu____5140 = FStar_Syntax_Subst.compress t1  in
                   uu____5140.FStar_Syntax_Syntax.n  in
                 match uu____5139 with
                 | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
                     let ff = tac_fold_env d f env  in
                     let uu____5172 = ff hd1  in
                     bind uu____5172
                       (fun hd2  ->
                          let fa uu____5192 =
                            match uu____5192 with
                            | (a,q) ->
                                let uu____5205 = ff a  in
                                bind uu____5205 (fun a1  -> ret (a1, q))
                             in
                          let uu____5218 = mapM fa args  in
                          bind uu____5218
                            (fun args1  ->
                               ret (FStar_Syntax_Syntax.Tm_app (hd2, args1))))
                 | FStar_Syntax_Syntax.Tm_abs (bs,t2,k) ->
                     let uu____5278 = FStar_Syntax_Subst.open_term bs t2  in
                     (match uu____5278 with
                      | (bs1,t') ->
                          let uu____5287 =
                            let uu____5290 =
                              FStar_TypeChecker_Env.push_binders env bs1  in
                            tac_fold_env d f uu____5290 t'  in
                          bind uu____5287
                            (fun t''  ->
                               let uu____5294 =
                                 let uu____5295 =
                                   let uu____5312 =
                                     FStar_Syntax_Subst.close_binders bs1  in
                                   let uu____5313 =
                                     FStar_Syntax_Subst.close bs1 t''  in
                                   (uu____5312, uu____5313, k)  in
                                 FStar_Syntax_Syntax.Tm_abs uu____5295  in
                               ret uu____5294))
                 | FStar_Syntax_Syntax.Tm_arrow (bs,k) -> ret tn
                 | uu____5334 -> ret tn  in
               bind tn1
                 (fun tn2  ->
                    let t' =
                      let uu___331_5341 = t1  in
                      {
                        FStar_Syntax_Syntax.n = tn2;
                        FStar_Syntax_Syntax.pos =
                          (uu___331_5341.FStar_Syntax_Syntax.pos);
                        FStar_Syntax_Syntax.vars =
                          (uu___331_5341.FStar_Syntax_Syntax.vars)
                      }  in
                    if d = FStar_Tactics_Types.BottomUp
                    then f env t'
                    else ret t'))
  
let pointwise_rec :
  FStar_Tactics_Types.proofstate ->
    Prims.unit tac ->
      FStar_Options.optionstate ->
        FStar_TypeChecker_Env.env ->
          FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac
  =
  fun ps  ->
    fun tau  ->
      fun opts  ->
        fun env  ->
          fun t  ->
            let uu____5370 = FStar_TypeChecker_TcTerm.tc_term env t  in
            match uu____5370 with
            | (t1,lcomp,g) ->
                let uu____5382 =
                  (let uu____5385 =
                     FStar_Syntax_Util.is_pure_or_ghost_lcomp lcomp  in
                   Prims.op_Negation uu____5385) ||
                    (let uu____5387 = FStar_TypeChecker_Rel.is_trivial g  in
                     Prims.op_Negation uu____5387)
                   in
                if uu____5382
                then ret t1
                else
                  (let rewrite_eq =
                     let typ = lcomp.FStar_Syntax_Syntax.res_typ  in
                     let uu____5397 = new_uvar "pointwise_rec" env typ  in
                     bind uu____5397
                       (fun ut  ->
                          log ps
                            (fun uu____5408  ->
                               let uu____5409 =
                                 FStar_Syntax_Print.term_to_string t1  in
                               let uu____5410 =
                                 FStar_Syntax_Print.term_to_string ut  in
                               FStar_Util.print2
                                 "Pointwise_rec: making equality\n\t%s ==\n\t%s\n"
                                 uu____5409 uu____5410);
                          (let uu____5411 =
                             let uu____5414 =
                               let uu____5415 =
                                 FStar_TypeChecker_TcTerm.universe_of env typ
                                  in
                               FStar_Syntax_Util.mk_eq2 uu____5415 typ t1 ut
                                in
                             add_irrelevant_goal "pointwise_rec equation" env
                               uu____5414 opts
                              in
                           bind uu____5411
                             (fun uu____5418  ->
                                let uu____5419 =
                                  bind tau
                                    (fun uu____5425  ->
                                       let ut1 =
                                         FStar_TypeChecker_Normalize.reduce_uvar_solutions
                                           env ut
                                          in
                                       log ps
                                         (fun uu____5431  ->
                                            let uu____5432 =
                                              FStar_Syntax_Print.term_to_string
                                                t1
                                               in
                                            let uu____5433 =
                                              FStar_Syntax_Print.term_to_string
                                                ut1
                                               in
                                            FStar_Util.print2
                                              "Pointwise_rec: succeeded rewriting\n\t%s to\n\t%s\n"
                                              uu____5432 uu____5433);
                                       ret ut1)
                                   in
                                focus uu____5419)))
                      in
                   let uu____5434 = trytac' rewrite_eq  in
                   bind uu____5434
                     (fun x  ->
                        match x with
                        | FStar_Util.Inl "SKIP" -> ret t1
                        | FStar_Util.Inl e -> fail e
                        | FStar_Util.Inr x1 -> ret x1))
  
let pointwise :
  FStar_Tactics_Types.direction -> Prims.unit tac -> Prims.unit tac =
  fun d  ->
    fun tau  ->
      bind get
        (fun ps  ->
           let uu____5476 =
             match ps.FStar_Tactics_Types.goals with
             | g::gs -> (g, gs)
             | [] -> failwith "Pointwise: no goals"  in
           match uu____5476 with
           | (g,gs) ->
               let gt1 = g.FStar_Tactics_Types.goal_ty  in
               (log ps
                  (fun uu____5513  ->
                     let uu____5514 = FStar_Syntax_Print.term_to_string gt1
                        in
                     FStar_Util.print1 "Pointwise starting with %s\n"
                       uu____5514);
                bind dismiss_all
                  (fun uu____5517  ->
                     let uu____5518 =
                       tac_fold_env d
                         (pointwise_rec ps tau g.FStar_Tactics_Types.opts)
                         g.FStar_Tactics_Types.context gt1
                        in
                     bind uu____5518
                       (fun gt'  ->
                          log ps
                            (fun uu____5528  ->
                               let uu____5529 =
                                 FStar_Syntax_Print.term_to_string gt'  in
                               FStar_Util.print1
                                 "Pointwise seems to have succeded with %s\n"
                                 uu____5529);
                          (let uu____5530 = push_goals gs  in
                           bind uu____5530
                             (fun uu____5534  ->
                                add_goals
                                  [(let uu___333_5536 = g  in
                                    {
                                      FStar_Tactics_Types.context =
                                        (uu___333_5536.FStar_Tactics_Types.context);
                                      FStar_Tactics_Types.witness =
                                        (uu___333_5536.FStar_Tactics_Types.witness);
                                      FStar_Tactics_Types.goal_ty = gt';
                                      FStar_Tactics_Types.opts =
                                        (uu___333_5536.FStar_Tactics_Types.opts);
                                      FStar_Tactics_Types.is_guard =
                                        (uu___333_5536.FStar_Tactics_Types.is_guard)
                                    })]))))))
  
let trefl : Prims.unit tac =
  bind cur_goal
    (fun g  ->
       let uu____5556 =
         FStar_Syntax_Util.un_squash g.FStar_Tactics_Types.goal_ty  in
       match uu____5556 with
       | FStar_Pervasives_Native.Some t ->
           let uu____5568 = FStar_Syntax_Util.head_and_args' t  in
           (match uu____5568 with
            | (hd1,args) ->
                let uu____5601 =
                  let uu____5614 =
                    let uu____5615 = FStar_Syntax_Util.un_uinst hd1  in
                    uu____5615.FStar_Syntax_Syntax.n  in
                  (uu____5614, args)  in
                (match uu____5601 with
                 | (FStar_Syntax_Syntax.Tm_fvar
                    fv,uu____5629::(l,uu____5631)::(r,uu____5633)::[]) when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.eq2_lid
                     ->
                     let uu____5680 =
                       let uu____5681 =
                         do_unify g.FStar_Tactics_Types.context l r  in
                       Prims.op_Negation uu____5681  in
                     if uu____5680
                     then
                       let uu____5684 = tts g.FStar_Tactics_Types.context l
                          in
                       let uu____5685 = tts g.FStar_Tactics_Types.context r
                          in
                       fail2 "trefl: not a trivial equality (%s vs %s)"
                         uu____5684 uu____5685
                     else solve g FStar_Syntax_Util.exp_unit
                 | (hd2,uu____5688) ->
                     let uu____5705 = tts g.FStar_Tactics_Types.context t  in
                     fail1 "trefl: not an equality (%s)" uu____5705))
       | FStar_Pervasives_Native.None  -> fail "not an irrelevant goal")
  
let dup : Prims.unit tac =
  bind cur_goal
    (fun g  ->
       let uu____5713 =
         new_uvar "dup" g.FStar_Tactics_Types.context
           g.FStar_Tactics_Types.goal_ty
          in
       bind uu____5713
         (fun u  ->
            let g' =
              let uu___334_5720 = g  in
              {
                FStar_Tactics_Types.context =
                  (uu___334_5720.FStar_Tactics_Types.context);
                FStar_Tactics_Types.witness = u;
                FStar_Tactics_Types.goal_ty =
                  (uu___334_5720.FStar_Tactics_Types.goal_ty);
                FStar_Tactics_Types.opts =
                  (uu___334_5720.FStar_Tactics_Types.opts);
                FStar_Tactics_Types.is_guard =
                  (uu___334_5720.FStar_Tactics_Types.is_guard)
              }  in
            bind dismiss
              (fun uu____5723  ->
                 let uu____5724 =
                   let uu____5727 =
                     let uu____5728 =
                       FStar_TypeChecker_TcTerm.universe_of
                         g.FStar_Tactics_Types.context
                         g.FStar_Tactics_Types.goal_ty
                        in
                     FStar_Syntax_Util.mk_eq2 uu____5728
                       g.FStar_Tactics_Types.goal_ty u
                       g.FStar_Tactics_Types.witness
                      in
                   add_irrelevant_goal "dup equation"
                     g.FStar_Tactics_Types.context uu____5727
                     g.FStar_Tactics_Types.opts
                    in
                 bind uu____5724
                   (fun uu____5731  ->
                      let uu____5732 = add_goals [g']  in
                      bind uu____5732 (fun uu____5736  -> ret ())))))
  
let flip : Prims.unit tac =
  bind get
    (fun ps  ->
       match ps.FStar_Tactics_Types.goals with
       | g1::g2::gs ->
           set
             (let uu___335_5753 = ps  in
              {
                FStar_Tactics_Types.main_context =
                  (uu___335_5753.FStar_Tactics_Types.main_context);
                FStar_Tactics_Types.main_goal =
                  (uu___335_5753.FStar_Tactics_Types.main_goal);
                FStar_Tactics_Types.all_implicits =
                  (uu___335_5753.FStar_Tactics_Types.all_implicits);
                FStar_Tactics_Types.goals = (g2 :: g1 :: gs);
                FStar_Tactics_Types.smt_goals =
                  (uu___335_5753.FStar_Tactics_Types.smt_goals);
                FStar_Tactics_Types.depth =
                  (uu___335_5753.FStar_Tactics_Types.depth);
                FStar_Tactics_Types.__dump =
                  (uu___335_5753.FStar_Tactics_Types.__dump);
                FStar_Tactics_Types.psc =
                  (uu___335_5753.FStar_Tactics_Types.psc);
                FStar_Tactics_Types.entry_range =
                  (uu___335_5753.FStar_Tactics_Types.entry_range)
              })
       | uu____5754 -> fail "flip: less than 2 goals")
  
let later : Prims.unit tac =
  bind get
    (fun ps  ->
       match ps.FStar_Tactics_Types.goals with
       | [] -> ret ()
       | g::gs ->
           set
             (let uu___336_5769 = ps  in
              {
                FStar_Tactics_Types.main_context =
                  (uu___336_5769.FStar_Tactics_Types.main_context);
                FStar_Tactics_Types.main_goal =
                  (uu___336_5769.FStar_Tactics_Types.main_goal);
                FStar_Tactics_Types.all_implicits =
                  (uu___336_5769.FStar_Tactics_Types.all_implicits);
                FStar_Tactics_Types.goals = (FStar_List.append gs [g]);
                FStar_Tactics_Types.smt_goals =
                  (uu___336_5769.FStar_Tactics_Types.smt_goals);
                FStar_Tactics_Types.depth =
                  (uu___336_5769.FStar_Tactics_Types.depth);
                FStar_Tactics_Types.__dump =
                  (uu___336_5769.FStar_Tactics_Types.__dump);
                FStar_Tactics_Types.psc =
                  (uu___336_5769.FStar_Tactics_Types.psc);
                FStar_Tactics_Types.entry_range =
                  (uu___336_5769.FStar_Tactics_Types.entry_range)
              }))
  
let qed : Prims.unit tac =
  bind get
    (fun ps  ->
       match ps.FStar_Tactics_Types.goals with
       | [] -> ret ()
       | uu____5776 -> fail "Not done!")
  
let cases :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 tac
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
                                let uu___337_5976 = g  in
                                let uu____5977 =
                                  FStar_TypeChecker_Env.push_bv
                                    g.FStar_Tactics_Types.context v_p
                                   in
                                {
                                  FStar_Tactics_Types.context = uu____5977;
                                  FStar_Tactics_Types.witness =
                                    (uu___337_5976.FStar_Tactics_Types.witness);
                                  FStar_Tactics_Types.goal_ty =
                                    (uu___337_5976.FStar_Tactics_Types.goal_ty);
                                  FStar_Tactics_Types.opts =
                                    (uu___337_5976.FStar_Tactics_Types.opts);
                                  FStar_Tactics_Types.is_guard =
                                    (uu___337_5976.FStar_Tactics_Types.is_guard)
                                }  in
                              let g2 =
                                let uu___338_5979 = g  in
                                let uu____5980 =
                                  FStar_TypeChecker_Env.push_bv
                                    g.FStar_Tactics_Types.context v_q
                                   in
                                {
                                  FStar_Tactics_Types.context = uu____5980;
                                  FStar_Tactics_Types.witness =
                                    (uu___338_5979.FStar_Tactics_Types.witness);
                                  FStar_Tactics_Types.goal_ty =
                                    (uu___338_5979.FStar_Tactics_Types.goal_ty);
                                  FStar_Tactics_Types.opts =
                                    (uu___338_5979.FStar_Tactics_Types.opts);
                                  FStar_Tactics_Types.is_guard =
                                    (uu___338_5979.FStar_Tactics_Types.is_guard)
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
  
let set_options : Prims.string -> Prims.unit tac =
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
                 let uu___339_6067 = g  in
                 {
                   FStar_Tactics_Types.context =
                     (uu___339_6067.FStar_Tactics_Types.context);
                   FStar_Tactics_Types.witness =
                     (uu___339_6067.FStar_Tactics_Types.witness);
                   FStar_Tactics_Types.goal_ty =
                     (uu___339_6067.FStar_Tactics_Types.goal_ty);
                   FStar_Tactics_Types.opts = opts';
                   FStar_Tactics_Types.is_guard =
                     (uu___339_6067.FStar_Tactics_Types.is_guard)
                 }  in
               replace_cur g'
           | FStar_Getopt.Error err ->
               fail2 "Setting options `%s` failed: %s" s err
           | FStar_Getopt.Help  ->
               fail1 "Setting options `%s` failed (got `Help`?)" s)))
  
let top_env : FStar_TypeChecker_Env.env tac =
  bind get
    (fun ps  -> FStar_All.pipe_left ret ps.FStar_Tactics_Types.main_context)
  
let cur_env : FStar_TypeChecker_Env.env tac =
  bind cur_goal
    (fun g  -> FStar_All.pipe_left ret g.FStar_Tactics_Types.context)
  
let cur_goal' : FStar_Syntax_Syntax.typ tac =
  bind cur_goal
    (fun g  -> FStar_All.pipe_left ret g.FStar_Tactics_Types.goal_ty)
  
let cur_witness : FStar_Syntax_Syntax.term tac =
  bind cur_goal
    (fun g  -> FStar_All.pipe_left ret g.FStar_Tactics_Types.witness)
  
let unquote :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac
  =
  fun ty  ->
    fun tm  ->
      let uu____6103 =
        bind cur_goal
          (fun goal  ->
             let env =
               FStar_TypeChecker_Env.set_expected_typ
                 goal.FStar_Tactics_Types.context ty
                in
             let uu____6111 = __tc env tm  in
             bind uu____6111
               (fun uu____6131  ->
                  match uu____6131 with
                  | (tm1,typ,guard) ->
                      (FStar_TypeChecker_Rel.force_trivial_guard env guard;
                       ret tm1)))
         in
      FStar_All.pipe_left (wrap_err "unquote") uu____6103
  
let uvar_env :
  env ->
    FStar_Syntax_Syntax.typ FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.term tac
  =
  fun env  ->
    fun ty  ->
      let uu____6162 =
        match ty with
        | FStar_Pervasives_Native.Some ty1 -> ret ty1
        | FStar_Pervasives_Native.None  ->
            let uu____6168 =
              let uu____6169 = FStar_Syntax_Util.type_u ()  in
              FStar_All.pipe_left FStar_Pervasives_Native.fst uu____6169  in
            new_uvar "uvar_env.2" env uu____6168
         in
      bind uu____6162
        (fun typ  ->
           let uu____6181 = new_uvar "uvar_env" env typ  in
           bind uu____6181 (fun t  -> ret t))
  
let unshelve : FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun t  ->
    let uu____6193 =
      bind cur_goal
        (fun goal  ->
           let uu____6199 = __tc goal.FStar_Tactics_Types.context t  in
           bind uu____6199
             (fun uu____6219  ->
                match uu____6219 with
                | (t1,typ,guard) ->
                    let uu____6231 =
                      must_trivial goal.FStar_Tactics_Types.context guard  in
                    bind uu____6231
                      (fun uu____6236  ->
                         let uu____6237 =
                           let uu____6240 =
                             let uu___340_6241 = goal  in
                             let uu____6242 =
                               bnorm goal.FStar_Tactics_Types.context t1  in
                             let uu____6243 =
                               bnorm goal.FStar_Tactics_Types.context typ  in
                             {
                               FStar_Tactics_Types.context =
                                 (uu___340_6241.FStar_Tactics_Types.context);
                               FStar_Tactics_Types.witness = uu____6242;
                               FStar_Tactics_Types.goal_ty = uu____6243;
                               FStar_Tactics_Types.opts =
                                 (uu___340_6241.FStar_Tactics_Types.opts);
                               FStar_Tactics_Types.is_guard = false
                             }  in
                           [uu____6240]  in
                         add_goals uu____6237)))
       in
    FStar_All.pipe_left (wrap_err "unshelve") uu____6193
  
let unify :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool tac =
  fun t1  ->
    fun t2  ->
      bind get
        (fun ps  ->
           let uu____6261 =
             do_unify ps.FStar_Tactics_Types.main_context t1 t2  in
           ret uu____6261)
  
let launch_process :
  Prims.string -> Prims.string -> Prims.string -> Prims.string tac =
  fun prog  ->
    fun args  ->
      fun input  ->
        bind idtac
          (fun uu____6278  ->
             let uu____6279 = FStar_Options.unsafe_tactic_exec ()  in
             if uu____6279
             then
               let s =
                 FStar_Util.launch_process true "tactic_launch" prog args
                   input (fun uu____6285  -> fun uu____6286  -> false)
                  in
               ret s
             else
               fail
                 "launch_process: will not run anything unless --unsafe_tactic_exec is provided")
  
let goal_of_goal_ty :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      (FStar_Tactics_Types.goal,FStar_TypeChecker_Env.guard_t)
        FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun typ  ->
      let uu____6306 =
        FStar_TypeChecker_Util.new_implicit_var "proofstate_of_goal_ty"
          typ.FStar_Syntax_Syntax.pos env typ
         in
      match uu____6306 with
      | (u,uu____6324,g_u) ->
          let g =
            let uu____6339 = FStar_Options.peek ()  in
            {
              FStar_Tactics_Types.context = env;
              FStar_Tactics_Types.witness = u;
              FStar_Tactics_Types.goal_ty = typ;
              FStar_Tactics_Types.opts = uu____6339;
              FStar_Tactics_Types.is_guard = false
            }  in
          (g, g_u)
  
let proofstate_of_goal_ty :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      (FStar_Tactics_Types.proofstate,FStar_Syntax_Syntax.term)
        FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun typ  ->
      let uu____6354 = goal_of_goal_ty env typ  in
      match uu____6354 with
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
  