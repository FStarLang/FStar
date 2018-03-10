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
              FStar_Util.format1 "Location: %s\n" uu____287  in
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
              let uu____421 =
                let uu____428 =
                  let uu____433 =
                    let uu____434 =
                      FStar_List.map goal_to_json
                        ps.FStar_Tactics_Types.goals
                       in
                    FStar_Util.JsonList uu____434  in
                  ("goals", uu____433)  in
                let uu____437 =
                  let uu____444 =
                    let uu____449 =
                      let uu____450 =
                        FStar_List.map goal_to_json
                          ps.FStar_Tactics_Types.smt_goals
                         in
                      FStar_Util.JsonList uu____450  in
                    ("smt-goals", uu____449)  in
                  [uu____444]  in
                uu____428 :: uu____437  in
              ("depth", (FStar_Util.JsonInt (ps.FStar_Tactics_Types.depth)))
                :: uu____421
               in
            ("label", (FStar_Util.JsonStr msg)) :: uu____414  in
          let uu____473 =
            if ps.FStar_Tactics_Types.entry_range <> FStar_Range.dummyRange
            then
              let uu____486 =
                let uu____491 =
                  FStar_Range.json_of_def_range
                    ps.FStar_Tactics_Types.entry_range
                   in
                ("location", uu____491)  in
              [uu____486]
            else []  in
          FStar_List.append uu____407 uu____473  in
        FStar_Util.JsonAssoc uu____400
  
let (dump_proofstate :
  FStar_Tactics_Types.proofstate -> Prims.string -> Prims.unit) =
  fun ps  ->
    fun msg  ->
      FStar_Options.with_saved_options
        (fun uu____517  ->
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
         (let uu____538 = FStar_Tactics_Types.subst_proof_state subst1 ps  in
          dump_cur uu____538 msg);
         FStar_Tactics_Result.Success ((), ps))
  
let (print_proof_state : Prims.string -> Prims.unit tac) =
  fun msg  ->
    mk_tac
      (fun ps  ->
         let psc = ps.FStar_Tactics_Types.psc  in
         let subst1 = FStar_TypeChecker_Normalize.psc_subst psc  in
         (let uu____554 = FStar_Tactics_Types.subst_proof_state subst1 ps  in
          dump_proofstate uu____554 msg);
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
      let uu____589 = FStar_ST.op_Bang tac_verb_dbg  in
      match uu____589 with
      | FStar_Pervasives_Native.None  ->
          ((let uu____616 =
              let uu____619 =
                FStar_TypeChecker_Env.debug
                  ps.FStar_Tactics_Types.main_context
                  (FStar_Options.Other "TacVerbose")
                 in
              FStar_Pervasives_Native.Some uu____619  in
            FStar_ST.op_Colon_Equals tac_verb_dbg uu____616);
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
         (let uu____688 =
            FStar_TypeChecker_Env.debug ps.FStar_Tactics_Types.main_context
              (FStar_Options.Other "TacFail")
             in
          if uu____688
          then dump_proofstate ps (Prims.strcat "TACTIC FAILING: " msg)
          else ());
         FStar_Tactics_Result.Failed (msg, ps))
  
let fail1 : 'Auu____693 . Prims.string -> Prims.string -> 'Auu____693 tac =
  fun msg  ->
    fun x  -> let uu____704 = FStar_Util.format1 msg x  in fail uu____704
  
let fail2 :
  'Auu____709 .
    Prims.string -> Prims.string -> Prims.string -> 'Auu____709 tac
  =
  fun msg  ->
    fun x  ->
      fun y  -> let uu____724 = FStar_Util.format2 msg x y  in fail uu____724
  
let fail3 :
  'Auu____730 .
    Prims.string ->
      Prims.string -> Prims.string -> Prims.string -> 'Auu____730 tac
  =
  fun msg  ->
    fun x  ->
      fun y  ->
        fun z  ->
          let uu____749 = FStar_Util.format3 msg x y z  in fail uu____749
  
let fail4 :
  'Auu____756 .
    Prims.string ->
      Prims.string ->
        Prims.string -> Prims.string -> Prims.string -> 'Auu____756 tac
  =
  fun msg  ->
    fun x  ->
      fun y  ->
        fun z  ->
          fun w  ->
            let uu____779 = FStar_Util.format4 msg x y z w  in fail uu____779
  
let trytac' : 'a . 'a tac -> (Prims.string,'a) FStar_Util.either tac =
  fun t  ->
    mk_tac
      (fun ps  ->
         let tx = FStar_Syntax_Unionfind.new_transaction ()  in
         let uu____809 = run t ps  in
         match uu____809 with
         | FStar_Tactics_Result.Success (a,q) ->
             (FStar_Syntax_Unionfind.commit tx;
              FStar_Tactics_Result.Success ((FStar_Util.Inr a), q))
         | FStar_Tactics_Result.Failed (m,uu____830) ->
             (FStar_Syntax_Unionfind.rollback tx;
              FStar_Tactics_Result.Success ((FStar_Util.Inl m), ps)))
  
let trytac : 'a . 'a tac -> 'a FStar_Pervasives_Native.option tac =
  fun t  ->
    let uu____855 = trytac' t  in
    bind uu____855
      (fun r  ->
         match r with
         | FStar_Util.Inr v1 -> ret (FStar_Pervasives_Native.Some v1)
         | FStar_Util.Inl uu____882 -> ret FStar_Pervasives_Native.None)
  
let trytac_exn : 'a . 'a tac -> 'a FStar_Pervasives_Native.option tac =
  fun t  ->
    mk_tac
      (fun ps  ->
         try let uu____915 = trytac t  in run uu____915 ps
         with
         | FStar_Errors.Err (uu____931,msg) ->
             (log ps
                (fun uu____935  ->
                   FStar_Util.print1 "trytac_exn error: (%s)" msg);
              FStar_Tactics_Result.Success (FStar_Pervasives_Native.None, ps))
         | FStar_Errors.Error (uu____940,msg,uu____942) ->
             (log ps
                (fun uu____945  ->
                   FStar_Util.print1 "trytac_exn error: (%s)" msg);
              FStar_Tactics_Result.Success (FStar_Pervasives_Native.None, ps)))
  
let wrap_err : 'a . Prims.string -> 'a tac -> 'a tac =
  fun pref  ->
    fun t  ->
      mk_tac
        (fun ps  ->
           let uu____973 = run t ps  in
           match uu____973 with
           | FStar_Tactics_Result.Success (a,q) ->
               FStar_Tactics_Result.Success (a, q)
           | FStar_Tactics_Result.Failed (msg,q) ->
               FStar_Tactics_Result.Failed
                 ((Prims.strcat pref (Prims.strcat ": " msg)), q))
  
let (set : FStar_Tactics_Types.proofstate -> Prims.unit tac) =
  fun p  -> mk_tac (fun uu____990  -> FStar_Tactics_Result.Success ((), p)) 
let (do_unify :
  env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool tac)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let debug_on uu____1007 =
          let uu____1008 =
            FStar_Options.set_options FStar_Options.Set
              "--debug_level Rel --debug_level RelCheck"
             in
          ()  in
        let debug_off uu____1012 =
          let uu____1013 = FStar_Options.set_options FStar_Options.Reset ""
             in
          ()  in
        (let uu____1015 =
           FStar_TypeChecker_Env.debug env (FStar_Options.Other "1346")  in
         if uu____1015
         then
           (debug_on ();
            (let uu____1017 = FStar_Syntax_Print.term_to_string t1  in
             let uu____1018 = FStar_Syntax_Print.term_to_string t2  in
             FStar_Util.print2 "%%%%%%%%do_unify %s =? %s\n" uu____1017
               uu____1018))
         else ());
        (try
           let res = FStar_TypeChecker_Rel.teq_nosmt env t1 t2  in
           debug_off (); ret res
         with
         | FStar_Errors.Err (uu____1037,msg) ->
             (debug_off ();
              mlog
                (fun uu____1041  ->
                   FStar_Util.print1 ">> do_unify error, (%s)\n" msg)
                (fun uu____1043  -> ret false))
         | FStar_Errors.Error (uu____1044,msg,r) ->
             (debug_off ();
              mlog
                (fun uu____1050  ->
                   let uu____1051 = FStar_Range.string_of_range r  in
                   FStar_Util.print2 ">> do_unify error, (%s) at (%s)\n" msg
                     uu____1051) (fun uu____1053  -> ret false)))
  
let (trysolve :
  FStar_Tactics_Types.goal -> FStar_Syntax_Syntax.term -> Prims.bool tac) =
  fun goal  ->
    fun solution  ->
      do_unify goal.FStar_Tactics_Types.context solution
        goal.FStar_Tactics_Types.witness
  
let (dismiss : Prims.unit tac) =
  bind get
    (fun p  ->
       let uu____1069 =
         let uu___63_1070 = p  in
         let uu____1071 = FStar_List.tl p.FStar_Tactics_Types.goals  in
         {
           FStar_Tactics_Types.main_context =
             (uu___63_1070.FStar_Tactics_Types.main_context);
           FStar_Tactics_Types.main_goal =
             (uu___63_1070.FStar_Tactics_Types.main_goal);
           FStar_Tactics_Types.all_implicits =
             (uu___63_1070.FStar_Tactics_Types.all_implicits);
           FStar_Tactics_Types.goals = uu____1071;
           FStar_Tactics_Types.smt_goals =
             (uu___63_1070.FStar_Tactics_Types.smt_goals);
           FStar_Tactics_Types.depth =
             (uu___63_1070.FStar_Tactics_Types.depth);
           FStar_Tactics_Types.__dump =
             (uu___63_1070.FStar_Tactics_Types.__dump);
           FStar_Tactics_Types.psc = (uu___63_1070.FStar_Tactics_Types.psc);
           FStar_Tactics_Types.entry_range =
             (uu___63_1070.FStar_Tactics_Types.entry_range);
           FStar_Tactics_Types.guard_policy =
             (uu___63_1070.FStar_Tactics_Types.guard_policy)
         }  in
       set uu____1069)
  
let (solve :
  FStar_Tactics_Types.goal -> FStar_Syntax_Syntax.term -> Prims.unit tac) =
  fun goal  ->
    fun solution  ->
      let uu____1084 = trysolve goal solution  in
      bind uu____1084
        (fun b  ->
           if b
           then dismiss
           else
             (let uu____1092 =
                let uu____1093 =
                  tts goal.FStar_Tactics_Types.context solution  in
                let uu____1094 =
                  tts goal.FStar_Tactics_Types.context
                    goal.FStar_Tactics_Types.witness
                   in
                let uu____1095 =
                  tts goal.FStar_Tactics_Types.context
                    goal.FStar_Tactics_Types.goal_ty
                   in
                FStar_Util.format3 "%s does not solve %s : %s" uu____1093
                  uu____1094 uu____1095
                 in
              fail uu____1092))
  
let (dismiss_all : Prims.unit tac) =
  bind get
    (fun p  ->
       set
         (let uu___64_1102 = p  in
          {
            FStar_Tactics_Types.main_context =
              (uu___64_1102.FStar_Tactics_Types.main_context);
            FStar_Tactics_Types.main_goal =
              (uu___64_1102.FStar_Tactics_Types.main_goal);
            FStar_Tactics_Types.all_implicits =
              (uu___64_1102.FStar_Tactics_Types.all_implicits);
            FStar_Tactics_Types.goals = [];
            FStar_Tactics_Types.smt_goals =
              (uu___64_1102.FStar_Tactics_Types.smt_goals);
            FStar_Tactics_Types.depth =
              (uu___64_1102.FStar_Tactics_Types.depth);
            FStar_Tactics_Types.__dump =
              (uu___64_1102.FStar_Tactics_Types.__dump);
            FStar_Tactics_Types.psc = (uu___64_1102.FStar_Tactics_Types.psc);
            FStar_Tactics_Types.entry_range =
              (uu___64_1102.FStar_Tactics_Types.entry_range);
            FStar_Tactics_Types.guard_policy =
              (uu___64_1102.FStar_Tactics_Types.guard_policy)
          }))
  
let (nwarn : Prims.int FStar_ST.ref) =
  FStar_Util.mk_ref (Prims.parse_int "0") 
let (check_valid_goal : FStar_Tactics_Types.goal -> Prims.unit) =
  fun g  ->
    let uu____1119 = FStar_Options.defensive ()  in
    if uu____1119
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
        let uu____1131 = FStar_TypeChecker_Env.pop_bv e  in
        match uu____1131 with
        | FStar_Pervasives_Native.None  -> b3
        | FStar_Pervasives_Native.Some (bv,e1) ->
            let b4 =
              b3 &&
                (FStar_TypeChecker_Env.closed e1 bv.FStar_Syntax_Syntax.sort)
               in
            aux b4 e1
         in
      let uu____1149 =
        (let uu____1152 = aux b2 env  in Prims.op_Negation uu____1152) &&
          (let uu____1154 = FStar_ST.op_Bang nwarn  in
           uu____1154 < (Prims.parse_int "5"))
         in
      (if uu____1149
       then
         ((let uu____1175 =
             let uu____1180 =
               let uu____1181 = goal_to_string g  in
               FStar_Util.format1
                 "The following goal is ill-formed. Keeping calm and carrying on...\n<%s>\n\n"
                 uu____1181
                in
             (FStar_Errors.Warning_IllFormedGoal, uu____1180)  in
           FStar_Errors.log_issue
             (g.FStar_Tactics_Types.goal_ty).FStar_Syntax_Syntax.pos
             uu____1175);
          (let uu____1182 =
             let uu____1183 = FStar_ST.op_Bang nwarn  in
             uu____1183 + (Prims.parse_int "1")  in
           FStar_ST.op_Colon_Equals nwarn uu____1182))
       else ())
    else ()
  
let (add_goals : FStar_Tactics_Types.goal Prims.list -> Prims.unit tac) =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___65_1241 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___65_1241.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___65_1241.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___65_1241.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (FStar_List.append gs p.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___65_1241.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___65_1241.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___65_1241.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___65_1241.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___65_1241.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___65_1241.FStar_Tactics_Types.guard_policy)
            }))
  
let (add_smt_goals : FStar_Tactics_Types.goal Prims.list -> Prims.unit tac) =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___66_1259 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___66_1259.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___66_1259.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___66_1259.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___66_1259.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (FStar_List.append gs p.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___66_1259.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___66_1259.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___66_1259.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___66_1259.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___66_1259.FStar_Tactics_Types.guard_policy)
            }))
  
let (push_goals : FStar_Tactics_Types.goal Prims.list -> Prims.unit tac) =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___67_1277 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___67_1277.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___67_1277.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___67_1277.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (FStar_List.append p.FStar_Tactics_Types.goals gs);
              FStar_Tactics_Types.smt_goals =
                (uu___67_1277.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___67_1277.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___67_1277.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___67_1277.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___67_1277.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___67_1277.FStar_Tactics_Types.guard_policy)
            }))
  
let (push_smt_goals : FStar_Tactics_Types.goal Prims.list -> Prims.unit tac)
  =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___68_1295 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___68_1295.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___68_1295.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___68_1295.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___68_1295.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (FStar_List.append p.FStar_Tactics_Types.smt_goals gs);
              FStar_Tactics_Types.depth =
                (uu___68_1295.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___68_1295.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___68_1295.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___68_1295.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___68_1295.FStar_Tactics_Types.guard_policy)
            }))
  
let (replace_cur : FStar_Tactics_Types.goal -> Prims.unit tac) =
  fun g  -> bind dismiss (fun uu____1304  -> add_goals [g]) 
let (add_implicits : implicits -> Prims.unit tac) =
  fun i  ->
    bind get
      (fun p  ->
         set
           (let uu___69_1316 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___69_1316.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___69_1316.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (FStar_List.append i p.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___69_1316.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___69_1316.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___69_1316.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___69_1316.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___69_1316.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___69_1316.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___69_1316.FStar_Tactics_Types.guard_policy)
            }))
  
let (new_uvar :
  Prims.string ->
    env -> FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.term tac)
  =
  fun reason  ->
    fun env  ->
      fun typ  ->
        let uu____1342 =
          FStar_TypeChecker_Util.new_implicit_var reason
            typ.FStar_Syntax_Syntax.pos env typ
           in
        match uu____1342 with
        | (u,uu____1358,g_u) ->
            let uu____1372 =
              add_implicits g_u.FStar_TypeChecker_Env.implicits  in
            bind uu____1372 (fun uu____1376  -> ret u)
  
let (is_true : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____1380 = FStar_Syntax_Util.un_squash t  in
    match uu____1380 with
    | FStar_Pervasives_Native.Some t' ->
        let uu____1390 =
          let uu____1391 = FStar_Syntax_Subst.compress t'  in
          uu____1391.FStar_Syntax_Syntax.n  in
        (match uu____1390 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.true_lid
         | uu____1395 -> false)
    | uu____1396 -> false
  
let (is_false : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____1404 = FStar_Syntax_Util.un_squash t  in
    match uu____1404 with
    | FStar_Pervasives_Native.Some t' ->
        let uu____1414 =
          let uu____1415 = FStar_Syntax_Subst.compress t'  in
          uu____1415.FStar_Syntax_Syntax.n  in
        (match uu____1414 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.false_lid
         | uu____1419 -> false)
    | uu____1420 -> false
  
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
            let uu____1460 = env.FStar_TypeChecker_Env.universe_of env phi
               in
            FStar_Syntax_Util.mk_squash uu____1460 phi  in
          let uu____1461 = new_uvar reason env typ  in
          bind uu____1461
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
             let uu____1517 =
               (ps.FStar_Tactics_Types.main_context).FStar_TypeChecker_Env.type_of
                 e t
                in
             ret uu____1517
           with
           | FStar_Errors.Err (uu____1544,msg) ->
               let uu____1546 = tts e t  in
               let uu____1547 =
                 let uu____1548 = FStar_TypeChecker_Env.all_binders e  in
                 FStar_All.pipe_right uu____1548
                   (FStar_Syntax_Print.binders_to_string ", ")
                  in
               fail3 "Cannot type %s in context (%s). Error = (%s)"
                 uu____1546 uu____1547 msg
           | FStar_Errors.Error (uu____1555,msg,uu____1557) ->
               let uu____1558 = tts e t  in
               let uu____1559 =
                 let uu____1560 = FStar_TypeChecker_Env.all_binders e  in
                 FStar_All.pipe_right uu____1560
                   (FStar_Syntax_Print.binders_to_string ", ")
                  in
               fail3 "Cannot type %s in context (%s). Error = (%s)"
                 uu____1558 uu____1559 msg)
  
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
  
let (get_guard_policy : FStar_Tactics_Types.guard_policy tac) =
  bind get (fun ps  -> ret ps.FStar_Tactics_Types.guard_policy) 
let (set_guard_policy : FStar_Tactics_Types.guard_policy -> Prims.unit tac) =
  fun pol  ->
    bind get
      (fun ps  ->
         set
           (let uu___72_1594 = ps  in
            {
              FStar_Tactics_Types.main_context =
                (uu___72_1594.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___72_1594.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___72_1594.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___72_1594.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___72_1594.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___72_1594.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___72_1594.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___72_1594.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___72_1594.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy = pol
            }))
  
let with_policy : 'a . FStar_Tactics_Types.guard_policy -> 'a tac -> 'a tac =
  fun pol  ->
    fun t  ->
      bind get_guard_policy
        (fun old_pol  ->
           let uu____1616 = set_guard_policy pol  in
           bind uu____1616
             (fun uu____1620  ->
                bind t
                  (fun r  ->
                     let uu____1624 = set_guard_policy old_pol  in
                     bind uu____1624 (fun uu____1628  -> ret r))))
  
let (proc_guard :
  Prims.string ->
    env ->
      FStar_TypeChecker_Env.guard_t ->
        FStar_Options.optionstate -> Prims.unit tac)
  =
  fun reason  ->
    fun e  ->
      fun g  ->
        fun opts  ->
          let uu____1645 =
            let uu____1646 = FStar_TypeChecker_Rel.simplify_guard e g  in
            uu____1646.FStar_TypeChecker_Env.guard_f  in
          match uu____1645 with
          | FStar_TypeChecker_Common.Trivial  -> ret ()
          | FStar_TypeChecker_Common.NonTrivial f ->
              let uu____1650 = istrivial e f  in
              if uu____1650
              then ret ()
              else
                bind get
                  (fun ps  ->
                     match ps.FStar_Tactics_Types.guard_policy with
                     | FStar_Tactics_Types.Drop  -> ret ()
                     | FStar_Tactics_Types.Goal  ->
                         let uu____1658 = mk_irrelevant_goal reason e f opts
                            in
                         bind uu____1658
                           (fun goal  ->
                              let goal1 =
                                let uu___73_1665 = goal  in
                                {
                                  FStar_Tactics_Types.context =
                                    (uu___73_1665.FStar_Tactics_Types.context);
                                  FStar_Tactics_Types.witness =
                                    (uu___73_1665.FStar_Tactics_Types.witness);
                                  FStar_Tactics_Types.goal_ty =
                                    (uu___73_1665.FStar_Tactics_Types.goal_ty);
                                  FStar_Tactics_Types.opts =
                                    (uu___73_1665.FStar_Tactics_Types.opts);
                                  FStar_Tactics_Types.is_guard = true
                                }  in
                              push_goals [goal1])
                     | FStar_Tactics_Types.SMT  ->
                         let uu____1666 = mk_irrelevant_goal reason e f opts
                            in
                         bind uu____1666
                           (fun goal  ->
                              let goal1 =
                                let uu___74_1673 = goal  in
                                {
                                  FStar_Tactics_Types.context =
                                    (uu___74_1673.FStar_Tactics_Types.context);
                                  FStar_Tactics_Types.witness =
                                    (uu___74_1673.FStar_Tactics_Types.witness);
                                  FStar_Tactics_Types.goal_ty =
                                    (uu___74_1673.FStar_Tactics_Types.goal_ty);
                                  FStar_Tactics_Types.opts =
                                    (uu___74_1673.FStar_Tactics_Types.opts);
                                  FStar_Tactics_Types.is_guard = true
                                }  in
                              push_smt_goals [goal1])
                     | FStar_Tactics_Types.Force  ->
                         (try
                            let uu____1681 =
                              let uu____1682 =
                                let uu____1683 =
                                  FStar_TypeChecker_Rel.discharge_guard_no_smt
                                    e g
                                   in
                                FStar_All.pipe_left
                                  FStar_TypeChecker_Rel.is_trivial uu____1683
                                 in
                              Prims.op_Negation uu____1682  in
                            if uu____1681
                            then
                              mlog
                                (fun uu____1688  ->
                                   let uu____1689 =
                                     FStar_TypeChecker_Rel.guard_to_string e
                                       g
                                      in
                                   FStar_Util.print1 "guard = %s\n"
                                     uu____1689)
                                (fun uu____1691  ->
                                   fail1 "Forcing the guard failed %s)"
                                     reason)
                            else ret ()
                          with
                          | uu____1698 ->
                              mlog
                                (fun uu____1701  ->
                                   let uu____1702 =
                                     FStar_TypeChecker_Rel.guard_to_string e
                                       g
                                      in
                                   FStar_Util.print1 "guard = %s\n"
                                     uu____1702)
                                (fun uu____1704  ->
                                   fail1 "Forcing the guard failed (%s)"
                                     reason)))
  
let (tc : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.typ tac) =
  fun t  ->
    let uu____1712 =
      bind cur_goal
        (fun goal  ->
           let uu____1718 = __tc goal.FStar_Tactics_Types.context t  in
           bind uu____1718
             (fun uu____1738  ->
                match uu____1738 with
                | (t1,typ,guard) ->
                    let uu____1750 =
                      proc_guard "tc" goal.FStar_Tactics_Types.context guard
                        goal.FStar_Tactics_Types.opts
                       in
                    bind uu____1750 (fun uu____1754  -> ret typ)))
       in
    FStar_All.pipe_left (wrap_err "tc") uu____1712
  
let (add_irrelevant_goal :
  Prims.string ->
    env ->
      FStar_Syntax_Syntax.typ -> FStar_Options.optionstate -> Prims.unit tac)
  =
  fun reason  ->
    fun env  ->
      fun phi  ->
        fun opts  ->
          let uu____1775 = mk_irrelevant_goal reason env phi opts  in
          bind uu____1775 (fun goal  -> add_goals [goal])
  
let (trivial : Prims.unit tac) =
  bind cur_goal
    (fun goal  ->
       let uu____1787 =
         istrivial goal.FStar_Tactics_Types.context
           goal.FStar_Tactics_Types.goal_ty
          in
       if uu____1787
       then solve goal FStar_Syntax_Util.exp_unit
       else
         (let uu____1791 =
            tts goal.FStar_Tactics_Types.context
              goal.FStar_Tactics_Types.goal_ty
             in
          fail1 "Not a trivial goal: %s" uu____1791))
  
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
          let uu____1812 =
            let uu____1813 = FStar_TypeChecker_Rel.simplify_guard e g  in
            uu____1813.FStar_TypeChecker_Env.guard_f  in
          match uu____1812 with
          | FStar_TypeChecker_Common.Trivial  ->
              ret FStar_Pervasives_Native.None
          | FStar_TypeChecker_Common.NonTrivial f ->
              let uu____1821 = istrivial e f  in
              if uu____1821
              then ret FStar_Pervasives_Native.None
              else
                (let uu____1829 = mk_irrelevant_goal reason e f opts  in
                 bind uu____1829
                   (fun goal  ->
                      ret
                        (FStar_Pervasives_Native.Some
                           (let uu___77_1839 = goal  in
                            {
                              FStar_Tactics_Types.context =
                                (uu___77_1839.FStar_Tactics_Types.context);
                              FStar_Tactics_Types.witness =
                                (uu___77_1839.FStar_Tactics_Types.witness);
                              FStar_Tactics_Types.goal_ty =
                                (uu___77_1839.FStar_Tactics_Types.goal_ty);
                              FStar_Tactics_Types.opts =
                                (uu___77_1839.FStar_Tactics_Types.opts);
                              FStar_Tactics_Types.is_guard = true
                            }))))
  
let (smt : Prims.unit tac) =
  bind cur_goal
    (fun g  ->
       let uu____1847 = is_irrelevant g  in
       if uu____1847
       then bind dismiss (fun uu____1851  -> add_smt_goals [g])
       else
         (let uu____1853 =
            tts g.FStar_Tactics_Types.context g.FStar_Tactics_Types.goal_ty
             in
          fail1 "goal is not irrelevant: cannot dispatch to smt (%s)"
            uu____1853))
  
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
             let uu____1894 =
               try
                 let uu____1928 =
                   let uu____1937 = FStar_BigInt.to_int_fs n1  in
                   FStar_List.splitAt uu____1937 p.FStar_Tactics_Types.goals
                    in
                 ret uu____1928
               with | uu____1959 -> fail "divide: not enough goals"  in
             bind uu____1894
               (fun uu____1986  ->
                  match uu____1986 with
                  | (lgs,rgs) ->
                      let lp =
                        let uu___78_2012 = p  in
                        {
                          FStar_Tactics_Types.main_context =
                            (uu___78_2012.FStar_Tactics_Types.main_context);
                          FStar_Tactics_Types.main_goal =
                            (uu___78_2012.FStar_Tactics_Types.main_goal);
                          FStar_Tactics_Types.all_implicits =
                            (uu___78_2012.FStar_Tactics_Types.all_implicits);
                          FStar_Tactics_Types.goals = lgs;
                          FStar_Tactics_Types.smt_goals = [];
                          FStar_Tactics_Types.depth =
                            (uu___78_2012.FStar_Tactics_Types.depth);
                          FStar_Tactics_Types.__dump =
                            (uu___78_2012.FStar_Tactics_Types.__dump);
                          FStar_Tactics_Types.psc =
                            (uu___78_2012.FStar_Tactics_Types.psc);
                          FStar_Tactics_Types.entry_range =
                            (uu___78_2012.FStar_Tactics_Types.entry_range);
                          FStar_Tactics_Types.guard_policy =
                            (uu___78_2012.FStar_Tactics_Types.guard_policy)
                        }  in
                      let rp =
                        let uu___79_2014 = p  in
                        {
                          FStar_Tactics_Types.main_context =
                            (uu___79_2014.FStar_Tactics_Types.main_context);
                          FStar_Tactics_Types.main_goal =
                            (uu___79_2014.FStar_Tactics_Types.main_goal);
                          FStar_Tactics_Types.all_implicits =
                            (uu___79_2014.FStar_Tactics_Types.all_implicits);
                          FStar_Tactics_Types.goals = rgs;
                          FStar_Tactics_Types.smt_goals = [];
                          FStar_Tactics_Types.depth =
                            (uu___79_2014.FStar_Tactics_Types.depth);
                          FStar_Tactics_Types.__dump =
                            (uu___79_2014.FStar_Tactics_Types.__dump);
                          FStar_Tactics_Types.psc =
                            (uu___79_2014.FStar_Tactics_Types.psc);
                          FStar_Tactics_Types.entry_range =
                            (uu___79_2014.FStar_Tactics_Types.entry_range);
                          FStar_Tactics_Types.guard_policy =
                            (uu___79_2014.FStar_Tactics_Types.guard_policy)
                        }  in
                      let uu____2015 = set lp  in
                      bind uu____2015
                        (fun uu____2023  ->
                           bind l
                             (fun a  ->
                                bind get
                                  (fun lp'  ->
                                     let uu____2037 = set rp  in
                                     bind uu____2037
                                       (fun uu____2045  ->
                                          bind r
                                            (fun b  ->
                                               bind get
                                                 (fun rp'  ->
                                                    let p' =
                                                      let uu___80_2061 = p
                                                         in
                                                      {
                                                        FStar_Tactics_Types.main_context
                                                          =
                                                          (uu___80_2061.FStar_Tactics_Types.main_context);
                                                        FStar_Tactics_Types.main_goal
                                                          =
                                                          (uu___80_2061.FStar_Tactics_Types.main_goal);
                                                        FStar_Tactics_Types.all_implicits
                                                          =
                                                          (uu___80_2061.FStar_Tactics_Types.all_implicits);
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
                                                          (uu___80_2061.FStar_Tactics_Types.depth);
                                                        FStar_Tactics_Types.__dump
                                                          =
                                                          (uu___80_2061.FStar_Tactics_Types.__dump);
                                                        FStar_Tactics_Types.psc
                                                          =
                                                          (uu___80_2061.FStar_Tactics_Types.psc);
                                                        FStar_Tactics_Types.entry_range
                                                          =
                                                          (uu___80_2061.FStar_Tactics_Types.entry_range);
                                                        FStar_Tactics_Types.guard_policy
                                                          =
                                                          (uu___80_2061.FStar_Tactics_Types.guard_policy)
                                                      }  in
                                                    let uu____2062 = set p'
                                                       in
                                                    bind uu____2062
                                                      (fun uu____2070  ->
                                                         ret (a, b))))))))))
  
let focus : 'a . 'a tac -> 'a tac =
  fun f  ->
    let uu____2088 = divide FStar_BigInt.one f idtac  in
    bind uu____2088
      (fun uu____2101  -> match uu____2101 with | (a,()) -> ret a)
  
let rec map : 'a . 'a tac -> 'a Prims.list tac =
  fun tau  ->
    bind get
      (fun p  ->
         match p.FStar_Tactics_Types.goals with
         | [] -> ret []
         | uu____2135::uu____2136 ->
             let uu____2139 =
               let uu____2148 = map tau  in
               divide FStar_BigInt.one tau uu____2148  in
             bind uu____2139
               (fun uu____2166  ->
                  match uu____2166 with | (h,t) -> ret (h :: t)))
  
let (seq : Prims.unit tac -> Prims.unit tac -> Prims.unit tac) =
  fun t1  ->
    fun t2  ->
      let uu____2203 =
        bind t1
          (fun uu____2208  ->
             let uu____2209 = map t2  in
             bind uu____2209 (fun uu____2217  -> ret ()))
         in
      focus uu____2203
  
let (intro : FStar_Syntax_Syntax.binder tac) =
  let uu____2224 =
    bind cur_goal
      (fun goal  ->
         let uu____2233 =
           FStar_Syntax_Util.arrow_one goal.FStar_Tactics_Types.goal_ty  in
         match uu____2233 with
         | FStar_Pervasives_Native.Some (b,c) ->
             let uu____2248 =
               let uu____2249 = FStar_Syntax_Util.is_total_comp c  in
               Prims.op_Negation uu____2249  in
             if uu____2248
             then fail "Codomain is effectful"
             else
               (let env' =
                  FStar_TypeChecker_Env.push_binders
                    goal.FStar_Tactics_Types.context [b]
                   in
                let typ' = comp_to_typ c  in
                let uu____2255 = new_uvar "intro" env' typ'  in
                bind uu____2255
                  (fun u  ->
                     let uu____2261 =
                       let uu____2264 =
                         FStar_Syntax_Util.abs [b] u
                           FStar_Pervasives_Native.None
                          in
                       trysolve goal uu____2264  in
                     bind uu____2261
                       (fun bb  ->
                          if bb
                          then
                            let uu____2270 =
                              let uu____2273 =
                                let uu___83_2274 = goal  in
                                let uu____2275 = bnorm env' u  in
                                let uu____2276 = bnorm env' typ'  in
                                {
                                  FStar_Tactics_Types.context = env';
                                  FStar_Tactics_Types.witness = uu____2275;
                                  FStar_Tactics_Types.goal_ty = uu____2276;
                                  FStar_Tactics_Types.opts =
                                    (uu___83_2274.FStar_Tactics_Types.opts);
                                  FStar_Tactics_Types.is_guard =
                                    (uu___83_2274.FStar_Tactics_Types.is_guard)
                                }  in
                              replace_cur uu____2273  in
                            bind uu____2270 (fun uu____2278  -> ret b)
                          else fail "unification failed")))
         | FStar_Pervasives_Native.None  ->
             let uu____2284 =
               tts goal.FStar_Tactics_Types.context
                 goal.FStar_Tactics_Types.goal_ty
                in
             fail1 "goal is not an arrow (%s)" uu____2284)
     in
  FStar_All.pipe_left (wrap_err "intro") uu____2224 
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
       (let uu____2315 =
          FStar_Syntax_Util.arrow_one goal.FStar_Tactics_Types.goal_ty  in
        match uu____2315 with
        | FStar_Pervasives_Native.Some (b,c) ->
            let uu____2334 =
              let uu____2335 = FStar_Syntax_Util.is_total_comp c  in
              Prims.op_Negation uu____2335  in
            if uu____2334
            then fail "Codomain is effectful"
            else
              (let bv =
                 FStar_Syntax_Syntax.gen_bv "__recf"
                   FStar_Pervasives_Native.None
                   goal.FStar_Tactics_Types.goal_ty
                  in
               let bs =
                 let uu____2351 = FStar_Syntax_Syntax.mk_binder bv  in
                 [uu____2351; b]  in
               let env' =
                 FStar_TypeChecker_Env.push_binders
                   goal.FStar_Tactics_Types.context bs
                  in
               let uu____2353 =
                 let uu____2356 = comp_to_typ c  in
                 new_uvar "intro_rec" env' uu____2356  in
               bind uu____2353
                 (fun u  ->
                    let lb =
                      let uu____2371 =
                        FStar_Syntax_Util.abs [b] u
                          FStar_Pervasives_Native.None
                         in
                      FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl bv) []
                        goal.FStar_Tactics_Types.goal_ty
                        FStar_Parser_Const.effect_Tot_lid uu____2371 []
                        FStar_Range.dummyRange
                       in
                    let body = FStar_Syntax_Syntax.bv_to_name bv  in
                    let uu____2377 =
                      FStar_Syntax_Subst.close_let_rec [lb] body  in
                    match uu____2377 with
                    | (lbs,body1) ->
                        let tm =
                          FStar_Syntax_Syntax.mk
                            (FStar_Syntax_Syntax.Tm_let ((true, lbs), body1))
                            FStar_Pervasives_Native.None
                            (goal.FStar_Tactics_Types.witness).FStar_Syntax_Syntax.pos
                           in
                        let uu____2407 = trysolve goal tm  in
                        bind uu____2407
                          (fun bb  ->
                             if bb
                             then
                               let uu____2423 =
                                 let uu____2426 =
                                   let uu___84_2427 = goal  in
                                   let uu____2428 = bnorm env' u  in
                                   let uu____2429 =
                                     let uu____2430 = comp_to_typ c  in
                                     bnorm env' uu____2430  in
                                   {
                                     FStar_Tactics_Types.context = env';
                                     FStar_Tactics_Types.witness = uu____2428;
                                     FStar_Tactics_Types.goal_ty = uu____2429;
                                     FStar_Tactics_Types.opts =
                                       (uu___84_2427.FStar_Tactics_Types.opts);
                                     FStar_Tactics_Types.is_guard =
                                       (uu___84_2427.FStar_Tactics_Types.is_guard)
                                   }  in
                                 replace_cur uu____2426  in
                               bind uu____2423
                                 (fun uu____2437  ->
                                    let uu____2438 =
                                      let uu____2443 =
                                        FStar_Syntax_Syntax.mk_binder bv  in
                                      (uu____2443, b)  in
                                    ret uu____2438)
                             else fail "intro_rec: unification failed")))
        | FStar_Pervasives_Native.None  ->
            let uu____2457 =
              tts goal.FStar_Tactics_Types.context
                goal.FStar_Tactics_Types.goal_ty
               in
            fail1 "intro_rec: goal is not an arrow (%s)" uu____2457))
  
let (norm : FStar_Syntax_Embeddings.norm_step Prims.list -> Prims.unit tac) =
  fun s  ->
    bind cur_goal
      (fun goal  ->
         mlog
           (fun uu____2477  ->
              let uu____2478 =
                FStar_Syntax_Print.term_to_string
                  goal.FStar_Tactics_Types.witness
                 in
              FStar_Util.print1 "norm: witness = %s\n" uu____2478)
           (fun uu____2483  ->
              let steps =
                let uu____2487 = FStar_TypeChecker_Normalize.tr_norm_steps s
                   in
                FStar_List.append
                  [FStar_TypeChecker_Normalize.Reify;
                  FStar_TypeChecker_Normalize.UnfoldTac] uu____2487
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
                (let uu___85_2494 = goal  in
                 {
                   FStar_Tactics_Types.context =
                     (uu___85_2494.FStar_Tactics_Types.context);
                   FStar_Tactics_Types.witness = w;
                   FStar_Tactics_Types.goal_ty = t;
                   FStar_Tactics_Types.opts =
                     (uu___85_2494.FStar_Tactics_Types.opts);
                   FStar_Tactics_Types.is_guard =
                     (uu___85_2494.FStar_Tactics_Types.is_guard)
                 })))
  
let (norm_term_env :
  env ->
    FStar_Syntax_Embeddings.norm_step Prims.list ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac)
  =
  fun e  ->
    fun s  ->
      fun t  ->
        let uu____2512 =
          mlog
            (fun uu____2517  ->
               let uu____2518 = FStar_Syntax_Print.term_to_string t  in
               FStar_Util.print1 "norm_term: tm = %s\n" uu____2518)
            (fun uu____2520  ->
               bind get
                 (fun ps  ->
                    let opts =
                      match ps.FStar_Tactics_Types.goals with
                      | g::uu____2526 -> g.FStar_Tactics_Types.opts
                      | uu____2529 -> FStar_Options.peek ()  in
                    mlog
                      (fun uu____2534  ->
                         let uu____2535 =
                           tts ps.FStar_Tactics_Types.main_context t  in
                         FStar_Util.print1 "norm_term_env: t = %s\n"
                           uu____2535)
                      (fun uu____2538  ->
                         let uu____2539 = __tc e t  in
                         bind uu____2539
                           (fun uu____2559  ->
                              match uu____2559 with
                              | (t1,uu____2569,guard) ->
                                  let uu____2571 =
                                    proc_guard "norm_term_env" e guard opts
                                     in
                                  bind uu____2571
                                    (fun uu____2577  ->
                                       let steps =
                                         let uu____2581 =
                                           FStar_TypeChecker_Normalize.tr_norm_steps
                                             s
                                            in
                                         FStar_List.append
                                           [FStar_TypeChecker_Normalize.Reify;
                                           FStar_TypeChecker_Normalize.UnfoldTac]
                                           uu____2581
                                          in
                                       let t2 =
                                         normalize steps
                                           ps.FStar_Tactics_Types.main_context
                                           t1
                                          in
                                       ret t2)))))
           in
        FStar_All.pipe_left (wrap_err "norm_term") uu____2512
  
let (refine_intro : Prims.unit tac) =
  let uu____2593 =
    bind cur_goal
      (fun g  ->
         let uu____2600 =
           FStar_TypeChecker_Rel.base_and_refinement
             g.FStar_Tactics_Types.context g.FStar_Tactics_Types.goal_ty
            in
         match uu____2600 with
         | (uu____2613,FStar_Pervasives_Native.None ) ->
             fail "not a refinement"
         | (t,FStar_Pervasives_Native.Some (bv,phi)) ->
             let g1 =
               let uu___86_2638 = g  in
               {
                 FStar_Tactics_Types.context =
                   (uu___86_2638.FStar_Tactics_Types.context);
                 FStar_Tactics_Types.witness =
                   (uu___86_2638.FStar_Tactics_Types.witness);
                 FStar_Tactics_Types.goal_ty = t;
                 FStar_Tactics_Types.opts =
                   (uu___86_2638.FStar_Tactics_Types.opts);
                 FStar_Tactics_Types.is_guard =
                   (uu___86_2638.FStar_Tactics_Types.is_guard)
               }  in
             let uu____2639 =
               let uu____2644 =
                 let uu____2649 =
                   let uu____2650 = FStar_Syntax_Syntax.mk_binder bv  in
                   [uu____2650]  in
                 FStar_Syntax_Subst.open_term uu____2649 phi  in
               match uu____2644 with
               | (bvs,phi1) ->
                   let uu____2657 =
                     let uu____2658 = FStar_List.hd bvs  in
                     FStar_Pervasives_Native.fst uu____2658  in
                   (uu____2657, phi1)
                in
             (match uu____2639 with
              | (bv1,phi1) ->
                  let uu____2671 =
                    let uu____2674 =
                      FStar_Syntax_Subst.subst
                        [FStar_Syntax_Syntax.NT
                           (bv1, (g.FStar_Tactics_Types.witness))] phi1
                       in
                    mk_irrelevant_goal "refine_intro refinement"
                      g.FStar_Tactics_Types.context uu____2674
                      g.FStar_Tactics_Types.opts
                     in
                  bind uu____2671
                    (fun g2  ->
                       bind dismiss (fun uu____2678  -> add_goals [g1; g2]))))
     in
  FStar_All.pipe_left (wrap_err "refine_intro") uu____2593 
let (__exact_now : Prims.bool -> FStar_Syntax_Syntax.term -> Prims.unit tac)
  =
  fun set_expected_typ1  ->
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
           let uu____2699 = __tc env t  in
           bind uu____2699
             (fun uu____2719  ->
                match uu____2719 with
                | (t1,typ,guard) ->
                    let uu____2731 =
                      proc_guard "__exact typing"
                        goal.FStar_Tactics_Types.context guard
                        goal.FStar_Tactics_Types.opts
                       in
                    bind uu____2731
                      (fun uu____2735  ->
                         mlog
                           (fun uu____2739  ->
                              let uu____2740 =
                                tts goal.FStar_Tactics_Types.context typ  in
                              let uu____2741 =
                                tts goal.FStar_Tactics_Types.context
                                  goal.FStar_Tactics_Types.goal_ty
                                 in
                              FStar_Util.print2 "exact: unifying %s and %s\n"
                                uu____2740 uu____2741)
                           (fun uu____2744  ->
                              let uu____2745 =
                                do_unify goal.FStar_Tactics_Types.context typ
                                  goal.FStar_Tactics_Types.goal_ty
                                 in
                              bind uu____2745
                                (fun b  ->
                                   if b
                                   then solve goal t1
                                   else
                                     (let uu____2753 =
                                        tts goal.FStar_Tactics_Types.context
                                          t1
                                         in
                                      let uu____2754 =
                                        tts goal.FStar_Tactics_Types.context
                                          typ
                                         in
                                      let uu____2755 =
                                        tts goal.FStar_Tactics_Types.context
                                          goal.FStar_Tactics_Types.goal_ty
                                         in
                                      let uu____2756 =
                                        tts goal.FStar_Tactics_Types.context
                                          goal.FStar_Tactics_Types.witness
                                         in
                                      fail4
                                        "%s : %s does not exactly solve the goal %s (witness = %s)"
                                        uu____2753 uu____2754 uu____2755
                                        uu____2756))))))
  
let (t_exact : Prims.bool -> FStar_Syntax_Syntax.term -> Prims.unit tac) =
  fun set_expected_typ1  ->
    fun tm  ->
      let uu____2767 =
        mlog
          (fun uu____2772  ->
             let uu____2773 = FStar_Syntax_Print.term_to_string tm  in
             FStar_Util.print1 "t_exact: tm = %s\n" uu____2773)
          (fun uu____2776  ->
             let uu____2777 =
               let uu____2784 = __exact_now set_expected_typ1 tm  in
               trytac' uu____2784  in
             bind uu____2777
               (fun uu___56_2793  ->
                  match uu___56_2793 with
                  | FStar_Util.Inr r -> ret ()
                  | FStar_Util.Inl e ->
                      let uu____2802 =
                        let uu____2809 =
                          let uu____2812 =
                            norm [FStar_Syntax_Embeddings.Delta]  in
                          bind uu____2812
                            (fun uu____2816  ->
                               bind refine_intro
                                 (fun uu____2818  ->
                                    __exact_now set_expected_typ1 tm))
                           in
                        trytac' uu____2809  in
                      bind uu____2802
                        (fun uu___55_2825  ->
                           match uu___55_2825 with
                           | FStar_Util.Inr r -> ret ()
                           | FStar_Util.Inl uu____2833 -> fail e)))
         in
      FStar_All.pipe_left (wrap_err "exact") uu____2767
  
let (uvar_free_in_goal :
  FStar_Syntax_Syntax.uvar -> FStar_Tactics_Types.goal -> Prims.bool) =
  fun u  ->
    fun g  ->
      if g.FStar_Tactics_Types.is_guard
      then false
      else
        (let free_uvars =
           let uu____2848 =
             let uu____2855 =
               FStar_Syntax_Free.uvars g.FStar_Tactics_Types.goal_ty  in
             FStar_Util.set_elements uu____2855  in
           FStar_List.map FStar_Pervasives_Native.fst uu____2848  in
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
          let uu____2915 = f x  in
          bind uu____2915
            (fun y  ->
               let uu____2923 = mapM f xs  in
               bind uu____2923 (fun ys  -> ret (y :: ys)))
  
exception NoUnif 
let (uu___is_NoUnif : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with | NoUnif  -> true | uu____2941 -> false
  
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
               (fun uu____2959  ->
                  let uu____2960 = FStar_Syntax_Print.term_to_string tm  in
                  FStar_Util.print1 ">>> Calling __exact(%s)\n" uu____2960)
               (fun uu____2963  ->
                  let uu____2964 =
                    let uu____2969 =
                      let uu____2972 = t_exact false tm  in
                      with_policy FStar_Tactics_Types.Force uu____2972  in
                    trytac_exn uu____2969  in
                  bind uu____2964
                    (fun uu___57_2979  ->
                       match uu___57_2979 with
                       | FStar_Pervasives_Native.Some r -> ret ()
                       | FStar_Pervasives_Native.None  ->
                           mlog
                             (fun uu____2987  ->
                                let uu____2988 =
                                  FStar_Syntax_Print.term_to_string typ  in
                                FStar_Util.print1 ">>> typ = %s\n" uu____2988)
                             (fun uu____2991  ->
                                let uu____2992 =
                                  FStar_Syntax_Util.arrow_one typ  in
                                match uu____2992 with
                                | FStar_Pervasives_Native.None  ->
                                    FStar_Exn.raise NoUnif
                                | FStar_Pervasives_Native.Some ((bv,aq),c) ->
                                    mlog
                                      (fun uu____3024  ->
                                         let uu____3025 =
                                           FStar_Syntax_Print.binder_to_string
                                             (bv, aq)
                                            in
                                         FStar_Util.print1
                                           "__apply: pushing binder %s\n"
                                           uu____3025)
                                      (fun uu____3028  ->
                                         let uu____3029 =
                                           let uu____3030 =
                                             FStar_Syntax_Util.is_total_comp
                                               c
                                              in
                                           Prims.op_Negation uu____3030  in
                                         if uu____3029
                                         then
                                           fail "apply: not total codomain"
                                         else
                                           (let uu____3034 =
                                              new_uvar "apply"
                                                goal.FStar_Tactics_Types.context
                                                bv.FStar_Syntax_Syntax.sort
                                               in
                                            bind uu____3034
                                              (fun u  ->
                                                 let tm' =
                                                   FStar_Syntax_Syntax.mk_Tm_app
                                                     tm [(u, aq)]
                                                     FStar_Pervasives_Native.None
                                                     tm.FStar_Syntax_Syntax.pos
                                                    in
                                                 let typ' =
                                                   let uu____3054 =
                                                     comp_to_typ c  in
                                                   FStar_All.pipe_left
                                                     (FStar_Syntax_Subst.subst
                                                        [FStar_Syntax_Syntax.NT
                                                           (bv, u)])
                                                     uu____3054
                                                    in
                                                 let uu____3055 =
                                                   __apply uopt tm' typ'  in
                                                 bind uu____3055
                                                   (fun uu____3063  ->
                                                      let u1 =
                                                        bnorm
                                                          goal.FStar_Tactics_Types.context
                                                          u
                                                         in
                                                      let uu____3065 =
                                                        let uu____3066 =
                                                          let uu____3069 =
                                                            let uu____3070 =
                                                              FStar_Syntax_Util.head_and_args
                                                                u1
                                                               in
                                                            FStar_Pervasives_Native.fst
                                                              uu____3070
                                                             in
                                                          FStar_Syntax_Subst.compress
                                                            uu____3069
                                                           in
                                                        uu____3066.FStar_Syntax_Syntax.n
                                                         in
                                                      match uu____3065 with
                                                      | FStar_Syntax_Syntax.Tm_uvar
                                                          (uvar,uu____3098)
                                                          ->
                                                          bind get
                                                            (fun ps  ->
                                                               let uu____3126
                                                                 =
                                                                 uopt &&
                                                                   (uvar_free
                                                                    uvar ps)
                                                                  in
                                                               if uu____3126
                                                               then ret ()
                                                               else
                                                                 (let uu____3130
                                                                    =
                                                                    let uu____3133
                                                                    =
                                                                    let uu___87_3134
                                                                    = goal
                                                                     in
                                                                    let uu____3135
                                                                    =
                                                                    bnorm
                                                                    goal.FStar_Tactics_Types.context
                                                                    u1  in
                                                                    let uu____3136
                                                                    =
                                                                    bnorm
                                                                    goal.FStar_Tactics_Types.context
                                                                    bv.FStar_Syntax_Syntax.sort
                                                                     in
                                                                    {
                                                                    FStar_Tactics_Types.context
                                                                    =
                                                                    (uu___87_3134.FStar_Tactics_Types.context);
                                                                    FStar_Tactics_Types.witness
                                                                    =
                                                                    uu____3135;
                                                                    FStar_Tactics_Types.goal_ty
                                                                    =
                                                                    uu____3136;
                                                                    FStar_Tactics_Types.opts
                                                                    =
                                                                    (uu___87_3134.FStar_Tactics_Types.opts);
                                                                    FStar_Tactics_Types.is_guard
                                                                    = false
                                                                    }  in
                                                                    [uu____3133]
                                                                     in
                                                                  add_goals
                                                                    uu____3130))
                                                      | t -> ret ()))))))))
  
let try_unif : 'a . 'a tac -> 'a tac -> 'a tac =
  fun t  ->
    fun t'  -> mk_tac (fun ps  -> try run t ps with | NoUnif  -> run t' ps)
  
let (apply : Prims.bool -> FStar_Syntax_Syntax.term -> Prims.unit tac) =
  fun uopt  ->
    fun tm  ->
      let uu____3182 =
        mlog
          (fun uu____3187  ->
             let uu____3188 = FStar_Syntax_Print.term_to_string tm  in
             FStar_Util.print1 "apply: tm = %s\n" uu____3188)
          (fun uu____3190  ->
             bind cur_goal
               (fun goal  ->
                  let uu____3194 = __tc goal.FStar_Tactics_Types.context tm
                     in
                  bind uu____3194
                    (fun uu____3216  ->
                       match uu____3216 with
                       | (tm1,typ,guard) ->
                           let typ1 =
                             bnorm goal.FStar_Tactics_Types.context typ  in
                           let uu____3229 =
                             let uu____3232 =
                               let uu____3235 = __apply uopt tm1 typ1  in
                               bind uu____3235
                                 (fun uu____3239  ->
                                    proc_guard "apply guard"
                                      goal.FStar_Tactics_Types.context guard
                                      goal.FStar_Tactics_Types.opts)
                                in
                             focus uu____3232  in
                           let uu____3240 =
                             let uu____3243 =
                               tts goal.FStar_Tactics_Types.context tm1  in
                             let uu____3244 =
                               tts goal.FStar_Tactics_Types.context typ1  in
                             let uu____3245 =
                               tts goal.FStar_Tactics_Types.context
                                 goal.FStar_Tactics_Types.goal_ty
                                in
                             fail3
                               "Cannot instantiate %s (of type %s) to match goal (%s)"
                               uu____3243 uu____3244 uu____3245
                              in
                           try_unif uu____3229 uu____3240)))
         in
      FStar_All.pipe_left (wrap_err "apply") uu____3182
  
let (apply_lemma : FStar_Syntax_Syntax.term -> Prims.unit tac) =
  fun tm  ->
    let uu____3257 =
      let uu____3260 =
        mlog
          (fun uu____3265  ->
             let uu____3266 = FStar_Syntax_Print.term_to_string tm  in
             FStar_Util.print1 "apply_lemma: tm = %s\n" uu____3266)
          (fun uu____3269  ->
             let is_unit_t t =
               let uu____3274 =
                 let uu____3275 = FStar_Syntax_Subst.compress t  in
                 uu____3275.FStar_Syntax_Syntax.n  in
               match uu____3274 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.unit_lid
                   -> true
               | uu____3279 -> false  in
             bind cur_goal
               (fun goal  ->
                  let uu____3283 = __tc goal.FStar_Tactics_Types.context tm
                     in
                  bind uu____3283
                    (fun uu____3305  ->
                       match uu____3305 with
                       | (tm1,t,guard) ->
                           let uu____3317 =
                             FStar_Syntax_Util.arrow_formals_comp t  in
                           (match uu____3317 with
                            | (bs,comp) ->
                                if
                                  Prims.op_Negation
                                    (FStar_Syntax_Util.is_lemma_comp comp)
                                then fail "not a lemma"
                                else
                                  (let uu____3347 =
                                     FStar_List.fold_left
                                       (fun uu____3393  ->
                                          fun uu____3394  ->
                                            match (uu____3393, uu____3394)
                                            with
                                            | ((uvs,guard1,subst1),(b,aq)) ->
                                                let b_t =
                                                  FStar_Syntax_Subst.subst
                                                    subst1
                                                    b.FStar_Syntax_Syntax.sort
                                                   in
                                                let uu____3497 =
                                                  is_unit_t b_t  in
                                                if uu____3497
                                                then
                                                  (((FStar_Syntax_Util.exp_unit,
                                                      aq) :: uvs), guard1,
                                                    ((FStar_Syntax_Syntax.NT
                                                        (b,
                                                          FStar_Syntax_Util.exp_unit))
                                                    :: subst1))
                                                else
                                                  (let uu____3535 =
                                                     FStar_TypeChecker_Util.new_implicit_var
                                                       "apply_lemma"
                                                       (goal.FStar_Tactics_Types.goal_ty).FStar_Syntax_Syntax.pos
                                                       goal.FStar_Tactics_Types.context
                                                       b_t
                                                      in
                                                   match uu____3535 with
                                                   | (u,uu____3565,g_u) ->
                                                       let uu____3579 =
                                                         FStar_TypeChecker_Rel.conj_guard
                                                           guard1 g_u
                                                          in
                                                       (((u, aq) :: uvs),
                                                         uu____3579,
                                                         ((FStar_Syntax_Syntax.NT
                                                             (b, u)) ::
                                                         subst1))))
                                       ([], guard, []) bs
                                      in
                                   match uu____3347 with
                                   | (uvs,implicits,subst1) ->
                                       let uvs1 = FStar_List.rev uvs  in
                                       let comp1 =
                                         FStar_Syntax_Subst.subst_comp subst1
                                           comp
                                          in
                                       let uu____3649 =
                                         let uu____3658 =
                                           let uu____3667 =
                                             FStar_Syntax_Util.comp_to_comp_typ
                                               comp1
                                              in
                                           uu____3667.FStar_Syntax_Syntax.effect_args
                                            in
                                         match uu____3658 with
                                         | pre::post::uu____3678 ->
                                             ((FStar_Pervasives_Native.fst
                                                 pre),
                                               (FStar_Pervasives_Native.fst
                                                  post))
                                         | uu____3719 ->
                                             failwith
                                               "apply_lemma: impossible: not a lemma"
                                          in
                                       (match uu____3649 with
                                        | (pre,post) ->
                                            let post1 =
                                              let uu____3751 =
                                                let uu____3760 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    FStar_Syntax_Util.exp_unit
                                                   in
                                                [uu____3760]  in
                                              FStar_Syntax_Util.mk_app post
                                                uu____3751
                                               in
                                            let uu____3761 =
                                              let uu____3764 =
                                                FStar_Syntax_Util.mk_squash
                                                  FStar_Syntax_Syntax.U_zero
                                                  post1
                                                 in
                                              do_unify
                                                goal.FStar_Tactics_Types.context
                                                uu____3764
                                                goal.FStar_Tactics_Types.goal_ty
                                               in
                                            bind uu____3761
                                              (fun b  ->
                                                 if Prims.op_Negation b
                                                 then
                                                   let uu____3772 =
                                                     tts
                                                       goal.FStar_Tactics_Types.context
                                                       tm1
                                                      in
                                                   let uu____3773 =
                                                     let uu____3774 =
                                                       FStar_Syntax_Util.mk_squash
                                                         FStar_Syntax_Syntax.U_zero
                                                         post1
                                                        in
                                                     tts
                                                       goal.FStar_Tactics_Types.context
                                                       uu____3774
                                                      in
                                                   let uu____3775 =
                                                     tts
                                                       goal.FStar_Tactics_Types.context
                                                       goal.FStar_Tactics_Types.goal_ty
                                                      in
                                                   fail3
                                                     "Cannot instantiate lemma %s (with postcondition: %s) to match goal (%s)"
                                                     uu____3772 uu____3773
                                                     uu____3775
                                                 else
                                                   (let uu____3777 =
                                                      add_implicits
                                                        implicits.FStar_TypeChecker_Env.implicits
                                                       in
                                                    bind uu____3777
                                                      (fun uu____3782  ->
                                                         let uu____3783 =
                                                           solve goal
                                                             FStar_Syntax_Util.exp_unit
                                                            in
                                                         bind uu____3783
                                                           (fun uu____3791 
                                                              ->
                                                              let is_free_uvar
                                                                uv t1 =
                                                                let free_uvars
                                                                  =
                                                                  let uu____3802
                                                                    =
                                                                    let uu____3809
                                                                    =
                                                                    FStar_Syntax_Free.uvars
                                                                    t1  in
                                                                    FStar_Util.set_elements
                                                                    uu____3809
                                                                     in
                                                                  FStar_List.map
                                                                    FStar_Pervasives_Native.fst
                                                                    uu____3802
                                                                   in
                                                                FStar_List.existsML
                                                                  (fun u  ->
                                                                    FStar_Syntax_Unionfind.equiv
                                                                    u uv)
                                                                  free_uvars
                                                                 in
                                                              let appears uv
                                                                goals =
                                                                FStar_List.existsML
                                                                  (fun g'  ->
                                                                    is_free_uvar
                                                                    uv
                                                                    g'.FStar_Tactics_Types.goal_ty)
                                                                  goals
                                                                 in
                                                              let checkone t1
                                                                goals =
                                                                let uu____3850
                                                                  =
                                                                  FStar_Syntax_Util.head_and_args
                                                                    t1
                                                                   in
                                                                match uu____3850
                                                                with
                                                                | (hd1,uu____3866)
                                                                    ->
                                                                    (
                                                                    match 
                                                                    hd1.FStar_Syntax_Syntax.n
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Tm_uvar
                                                                    (uv,uu____3888)
                                                                    ->
                                                                    appears
                                                                    uv goals
                                                                    | 
                                                                    uu____3913
                                                                    -> false)
                                                                 in
                                                              let uu____3914
                                                                =
                                                                FStar_All.pipe_right
                                                                  implicits.FStar_TypeChecker_Env.implicits
                                                                  (mapM
                                                                    (fun
                                                                    uu____3986
                                                                     ->
                                                                    match uu____3986
                                                                    with
                                                                    | 
                                                                    (_msg,env,_uvar,term,typ,uu____4014)
                                                                    ->
                                                                    let uu____4015
                                                                    =
                                                                    FStar_Syntax_Util.head_and_args
                                                                    term  in
                                                                    (match uu____4015
                                                                    with
                                                                    | 
                                                                    (hd1,uu____4041)
                                                                    ->
                                                                    let uu____4062
                                                                    =
                                                                    let uu____4063
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    hd1  in
                                                                    uu____4063.FStar_Syntax_Syntax.n
                                                                     in
                                                                    (match uu____4062
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Tm_uvar
                                                                    uu____4076
                                                                    ->
                                                                    let uu____4093
                                                                    =
                                                                    let uu____4102
                                                                    =
                                                                    let uu____4105
                                                                    =
                                                                    let uu___90_4106
                                                                    = goal
                                                                     in
                                                                    let uu____4107
                                                                    =
                                                                    bnorm
                                                                    goal.FStar_Tactics_Types.context
                                                                    term  in
                                                                    let uu____4108
                                                                    =
                                                                    bnorm
                                                                    goal.FStar_Tactics_Types.context
                                                                    typ  in
                                                                    {
                                                                    FStar_Tactics_Types.context
                                                                    =
                                                                    (uu___90_4106.FStar_Tactics_Types.context);
                                                                    FStar_Tactics_Types.witness
                                                                    =
                                                                    uu____4107;
                                                                    FStar_Tactics_Types.goal_ty
                                                                    =
                                                                    uu____4108;
                                                                    FStar_Tactics_Types.opts
                                                                    =
                                                                    (uu___90_4106.FStar_Tactics_Types.opts);
                                                                    FStar_Tactics_Types.is_guard
                                                                    =
                                                                    (uu___90_4106.FStar_Tactics_Types.is_guard)
                                                                    }  in
                                                                    [uu____4105]
                                                                     in
                                                                    (uu____4102,
                                                                    [])  in
                                                                    ret
                                                                    uu____4093
                                                                    | 
                                                                    uu____4121
                                                                    ->
                                                                    let g_typ
                                                                    =
                                                                    let uu____4123
                                                                    =
                                                                    FStar_Options.__temp_fast_implicits
                                                                    ()  in
                                                                    if
                                                                    uu____4123
                                                                    then
                                                                    FStar_TypeChecker_TcTerm.check_type_of_well_typed_term
                                                                    false env
                                                                    term typ
                                                                    else
                                                                    (let term1
                                                                    =
                                                                    bnorm env
                                                                    term  in
                                                                    let uu____4126
                                                                    =
                                                                    let uu____4133
                                                                    =
                                                                    FStar_TypeChecker_Env.set_expected_typ
                                                                    env typ
                                                                     in
                                                                    env.FStar_TypeChecker_Env.type_of
                                                                    uu____4133
                                                                    term1  in
                                                                    match uu____4126
                                                                    with
                                                                    | 
                                                                    (uu____4134,uu____4135,g_typ)
                                                                    -> g_typ)
                                                                     in
                                                                    let uu____4137
                                                                    =
                                                                    goal_from_guard
                                                                    "apply_lemma solved arg"
                                                                    goal.FStar_Tactics_Types.context
                                                                    g_typ
                                                                    goal.FStar_Tactics_Types.opts
                                                                     in
                                                                    bind
                                                                    uu____4137
                                                                    (fun
                                                                    uu___58_4153
                                                                     ->
                                                                    match uu___58_4153
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
                                                              bind uu____3914
                                                                (fun goals_ 
                                                                   ->
                                                                   let sub_goals
                                                                    =
                                                                    let uu____4221
                                                                    =
                                                                    FStar_List.map
                                                                    FStar_Pervasives_Native.fst
                                                                    goals_
                                                                     in
                                                                    FStar_List.flatten
                                                                    uu____4221
                                                                     in
                                                                   let smt_goals
                                                                    =
                                                                    let uu____4243
                                                                    =
                                                                    FStar_List.map
                                                                    FStar_Pervasives_Native.snd
                                                                    goals_
                                                                     in
                                                                    FStar_List.flatten
                                                                    uu____4243
                                                                     in
                                                                   let rec filter'
                                                                    a f xs =
                                                                    match xs
                                                                    with
                                                                    | 
                                                                    [] -> []
                                                                    | 
                                                                    x::xs1 ->
                                                                    let uu____4298
                                                                    = f x xs1
                                                                     in
                                                                    if
                                                                    uu____4298
                                                                    then
                                                                    let uu____4301
                                                                    =
                                                                    filter'
                                                                    () f xs1
                                                                     in x ::
                                                                    uu____4301
                                                                    else
                                                                    filter'
                                                                    () f xs1
                                                                     in
                                                                   let sub_goals1
                                                                    =
                                                                    Obj.magic
                                                                    (filter'
                                                                    ()
                                                                    (fun a438
                                                                     ->
                                                                    fun a439 
                                                                    ->
                                                                    (Obj.magic
                                                                    (fun g 
                                                                    ->
                                                                    fun goals
                                                                     ->
                                                                    let uu____4315
                                                                    =
                                                                    checkone
                                                                    g.FStar_Tactics_Types.witness
                                                                    goals  in
                                                                    Prims.op_Negation
                                                                    uu____4315))
                                                                    a438 a439)
                                                                    (Obj.magic
                                                                    sub_goals))
                                                                     in
                                                                   let uu____4316
                                                                    =
                                                                    proc_guard
                                                                    "apply_lemma guard"
                                                                    goal.FStar_Tactics_Types.context
                                                                    guard
                                                                    goal.FStar_Tactics_Types.opts
                                                                     in
                                                                   bind
                                                                    uu____4316
                                                                    (fun
                                                                    uu____4321
                                                                     ->
                                                                    let uu____4322
                                                                    =
                                                                    let uu____4325
                                                                    =
                                                                    let uu____4326
                                                                    =
                                                                    let uu____4327
                                                                    =
                                                                    FStar_Syntax_Util.mk_squash
                                                                    FStar_Syntax_Syntax.U_zero
                                                                    pre  in
                                                                    istrivial
                                                                    goal.FStar_Tactics_Types.context
                                                                    uu____4327
                                                                     in
                                                                    Prims.op_Negation
                                                                    uu____4326
                                                                     in
                                                                    if
                                                                    uu____4325
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
                                                                    uu____4322
                                                                    (fun
                                                                    uu____4333
                                                                     ->
                                                                    let uu____4334
                                                                    =
                                                                    add_smt_goals
                                                                    smt_goals
                                                                     in
                                                                    bind
                                                                    uu____4334
                                                                    (fun
                                                                    uu____4338
                                                                     ->
                                                                    add_goals
                                                                    sub_goals1))))))))))))))
         in
      focus uu____3260  in
    FStar_All.pipe_left (wrap_err "apply_lemma") uu____3257
  
let (destruct_eq' :
  FStar_Syntax_Syntax.typ ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun typ  ->
    let uu____4358 = FStar_Syntax_Util.destruct_typ_as_formula typ  in
    match uu____4358 with
    | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn
        (l,uu____4368::(e1,uu____4370)::(e2,uu____4372)::[])) when
        FStar_Ident.lid_equals l FStar_Parser_Const.eq2_lid ->
        FStar_Pervasives_Native.Some (e1, e2)
    | uu____4431 -> FStar_Pervasives_Native.None
  
let (destruct_eq :
  FStar_Syntax_Syntax.typ ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun typ  ->
    let uu____4453 = destruct_eq' typ  in
    match uu____4453 with
    | FStar_Pervasives_Native.Some t -> FStar_Pervasives_Native.Some t
    | FStar_Pervasives_Native.None  ->
        let uu____4483 = FStar_Syntax_Util.un_squash typ  in
        (match uu____4483 with
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
        let uu____4539 = FStar_TypeChecker_Env.pop_bv e1  in
        match uu____4539 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (bv',e') ->
            if FStar_Syntax_Syntax.bv_eq bvar bv'
            then FStar_Pervasives_Native.Some (e', [])
            else
              (let uu____4587 = aux e'  in
               FStar_Util.map_opt uu____4587
                 (fun uu____4611  ->
                    match uu____4611 with | (e'',bvs) -> (e'', (bv' :: bvs))))
         in
      let uu____4632 = aux e  in
      FStar_Util.map_opt uu____4632
        (fun uu____4656  ->
           match uu____4656 with | (e',bvs) -> (e', (FStar_List.rev bvs)))
  
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
          let uu____4711 = split_env b1 g.FStar_Tactics_Types.context  in
          FStar_Util.map_opt uu____4711
            (fun uu____4735  ->
               match uu____4735 with
               | (e0,bvs) ->
                   let s1 bv =
                     let uu___91_4752 = bv  in
                     let uu____4753 =
                       FStar_Syntax_Subst.subst s bv.FStar_Syntax_Syntax.sort
                        in
                     {
                       FStar_Syntax_Syntax.ppname =
                         (uu___91_4752.FStar_Syntax_Syntax.ppname);
                       FStar_Syntax_Syntax.index =
                         (uu___91_4752.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort = uu____4753
                     }  in
                   let bvs1 = FStar_List.map s1 bvs  in
                   let c = push_bvs e0 (b2 :: bvs1)  in
                   let w =
                     FStar_Syntax_Subst.subst s g.FStar_Tactics_Types.witness
                      in
                   let t =
                     FStar_Syntax_Subst.subst s g.FStar_Tactics_Types.goal_ty
                      in
                   let uu___92_4762 = g  in
                   {
                     FStar_Tactics_Types.context = c;
                     FStar_Tactics_Types.witness = w;
                     FStar_Tactics_Types.goal_ty = t;
                     FStar_Tactics_Types.opts =
                       (uu___92_4762.FStar_Tactics_Types.opts);
                     FStar_Tactics_Types.is_guard =
                       (uu___92_4762.FStar_Tactics_Types.is_guard)
                   })
  
let (rewrite : FStar_Syntax_Syntax.binder -> Prims.unit tac) =
  fun h  ->
    bind cur_goal
      (fun goal  ->
         let uu____4775 = h  in
         match uu____4775 with
         | (bv,uu____4779) ->
             mlog
               (fun uu____4783  ->
                  let uu____4784 = FStar_Syntax_Print.bv_to_string bv  in
                  let uu____4785 =
                    tts goal.FStar_Tactics_Types.context
                      bv.FStar_Syntax_Syntax.sort
                     in
                  FStar_Util.print2 "+++Rewrite %s : %s\n" uu____4784
                    uu____4785)
               (fun uu____4788  ->
                  let uu____4789 =
                    split_env bv goal.FStar_Tactics_Types.context  in
                  match uu____4789 with
                  | FStar_Pervasives_Native.None  ->
                      fail "rewrite: binder not found in environment"
                  | FStar_Pervasives_Native.Some (e0,bvs) ->
                      let uu____4818 =
                        destruct_eq bv.FStar_Syntax_Syntax.sort  in
                      (match uu____4818 with
                       | FStar_Pervasives_Native.Some (x,e) ->
                           let uu____4833 =
                             let uu____4834 = FStar_Syntax_Subst.compress x
                                in
                             uu____4834.FStar_Syntax_Syntax.n  in
                           (match uu____4833 with
                            | FStar_Syntax_Syntax.Tm_name x1 ->
                                let s = [FStar_Syntax_Syntax.NT (x1, e)]  in
                                let s1 bv1 =
                                  let uu___93_4847 = bv1  in
                                  let uu____4848 =
                                    FStar_Syntax_Subst.subst s
                                      bv1.FStar_Syntax_Syntax.sort
                                     in
                                  {
                                    FStar_Syntax_Syntax.ppname =
                                      (uu___93_4847.FStar_Syntax_Syntax.ppname);
                                    FStar_Syntax_Syntax.index =
                                      (uu___93_4847.FStar_Syntax_Syntax.index);
                                    FStar_Syntax_Syntax.sort = uu____4848
                                  }  in
                                let bvs1 = FStar_List.map s1 bvs  in
                                let uu____4854 =
                                  let uu___94_4855 = goal  in
                                  let uu____4856 = push_bvs e0 (bv :: bvs1)
                                     in
                                  let uu____4857 =
                                    FStar_Syntax_Subst.subst s
                                      goal.FStar_Tactics_Types.witness
                                     in
                                  let uu____4858 =
                                    FStar_Syntax_Subst.subst s
                                      goal.FStar_Tactics_Types.goal_ty
                                     in
                                  {
                                    FStar_Tactics_Types.context = uu____4856;
                                    FStar_Tactics_Types.witness = uu____4857;
                                    FStar_Tactics_Types.goal_ty = uu____4858;
                                    FStar_Tactics_Types.opts =
                                      (uu___94_4855.FStar_Tactics_Types.opts);
                                    FStar_Tactics_Types.is_guard =
                                      (uu___94_4855.FStar_Tactics_Types.is_guard)
                                  }  in
                                replace_cur uu____4854
                            | uu____4859 ->
                                fail
                                  "rewrite: Not an equality hypothesis with a variable on the LHS")
                       | uu____4860 ->
                           fail "rewrite: Not an equality hypothesis")))
  
let (rename_to :
  FStar_Syntax_Syntax.binder -> Prims.string -> Prims.unit tac) =
  fun b  ->
    fun s  ->
      bind cur_goal
        (fun goal  ->
           let uu____4885 = b  in
           match uu____4885 with
           | (bv,uu____4889) ->
               let bv' =
                 FStar_Syntax_Syntax.freshen_bv
                   (let uu___95_4893 = bv  in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (FStar_Ident.mk_ident
                           (s,
                             ((bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange)));
                      FStar_Syntax_Syntax.index =
                        (uu___95_4893.FStar_Syntax_Syntax.index);
                      FStar_Syntax_Syntax.sort =
                        (uu___95_4893.FStar_Syntax_Syntax.sort)
                    })
                  in
               let s1 =
                 let uu____4897 =
                   let uu____4898 =
                     let uu____4905 = FStar_Syntax_Syntax.bv_to_name bv'  in
                     (bv, uu____4905)  in
                   FStar_Syntax_Syntax.NT uu____4898  in
                 [uu____4897]  in
               let uu____4906 = subst_goal bv bv' s1 goal  in
               (match uu____4906 with
                | FStar_Pervasives_Native.None  ->
                    fail "rename_to: binder not found in environment"
                | FStar_Pervasives_Native.Some goal1 -> replace_cur goal1))
  
let (binder_retype : FStar_Syntax_Syntax.binder -> Prims.unit tac) =
  fun b  ->
    bind cur_goal
      (fun goal  ->
         let uu____4925 = b  in
         match uu____4925 with
         | (bv,uu____4929) ->
             let uu____4930 = split_env bv goal.FStar_Tactics_Types.context
                in
             (match uu____4930 with
              | FStar_Pervasives_Native.None  ->
                  fail "binder_retype: binder is not present in environment"
              | FStar_Pervasives_Native.Some (e0,bvs) ->
                  let uu____4959 = FStar_Syntax_Util.type_u ()  in
                  (match uu____4959 with
                   | (ty,u) ->
                       let uu____4968 = new_uvar "binder_retype" e0 ty  in
                       bind uu____4968
                         (fun t'  ->
                            let bv'' =
                              let uu___96_4978 = bv  in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___96_4978.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___96_4978.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = t'
                              }  in
                            let s =
                              let uu____4982 =
                                let uu____4983 =
                                  let uu____4990 =
                                    FStar_Syntax_Syntax.bv_to_name bv''  in
                                  (bv, uu____4990)  in
                                FStar_Syntax_Syntax.NT uu____4983  in
                              [uu____4982]  in
                            let bvs1 =
                              FStar_List.map
                                (fun b1  ->
                                   let uu___97_4998 = b1  in
                                   let uu____4999 =
                                     FStar_Syntax_Subst.subst s
                                       b1.FStar_Syntax_Syntax.sort
                                      in
                                   {
                                     FStar_Syntax_Syntax.ppname =
                                       (uu___97_4998.FStar_Syntax_Syntax.ppname);
                                     FStar_Syntax_Syntax.index =
                                       (uu___97_4998.FStar_Syntax_Syntax.index);
                                     FStar_Syntax_Syntax.sort = uu____4999
                                   }) bvs
                               in
                            let env' = push_bvs e0 (bv'' :: bvs1)  in
                            bind dismiss
                              (fun uu____5005  ->
                                 let uu____5006 =
                                   let uu____5009 =
                                     let uu____5012 =
                                       let uu___98_5013 = goal  in
                                       let uu____5014 =
                                         FStar_Syntax_Subst.subst s
                                           goal.FStar_Tactics_Types.witness
                                          in
                                       let uu____5015 =
                                         FStar_Syntax_Subst.subst s
                                           goal.FStar_Tactics_Types.goal_ty
                                          in
                                       {
                                         FStar_Tactics_Types.context = env';
                                         FStar_Tactics_Types.witness =
                                           uu____5014;
                                         FStar_Tactics_Types.goal_ty =
                                           uu____5015;
                                         FStar_Tactics_Types.opts =
                                           (uu___98_5013.FStar_Tactics_Types.opts);
                                         FStar_Tactics_Types.is_guard =
                                           (uu___98_5013.FStar_Tactics_Types.is_guard)
                                       }  in
                                     [uu____5012]  in
                                   add_goals uu____5009  in
                                 bind uu____5006
                                   (fun uu____5018  ->
                                      let uu____5019 =
                                        FStar_Syntax_Util.mk_eq2
                                          (FStar_Syntax_Syntax.U_succ u) ty
                                          bv.FStar_Syntax_Syntax.sort t'
                                         in
                                      add_irrelevant_goal
                                        "binder_retype equation" e0
                                        uu____5019
                                        goal.FStar_Tactics_Types.opts))))))
  
let (norm_binder_type :
  FStar_Syntax_Embeddings.norm_step Prims.list ->
    FStar_Syntax_Syntax.binder -> Prims.unit tac)
  =
  fun s  ->
    fun b  ->
      bind cur_goal
        (fun goal  ->
           let uu____5040 = b  in
           match uu____5040 with
           | (bv,uu____5044) ->
               let uu____5045 = split_env bv goal.FStar_Tactics_Types.context
                  in
               (match uu____5045 with
                | FStar_Pervasives_Native.None  ->
                    fail
                      "binder_retype: binder is not present in environment"
                | FStar_Pervasives_Native.Some (e0,bvs) ->
                    let steps =
                      let uu____5077 =
                        FStar_TypeChecker_Normalize.tr_norm_steps s  in
                      FStar_List.append
                        [FStar_TypeChecker_Normalize.Reify;
                        FStar_TypeChecker_Normalize.UnfoldTac] uu____5077
                       in
                    let sort' =
                      normalize steps e0 bv.FStar_Syntax_Syntax.sort  in
                    let bv' =
                      let uu___99_5082 = bv  in
                      {
                        FStar_Syntax_Syntax.ppname =
                          (uu___99_5082.FStar_Syntax_Syntax.ppname);
                        FStar_Syntax_Syntax.index =
                          (uu___99_5082.FStar_Syntax_Syntax.index);
                        FStar_Syntax_Syntax.sort = sort'
                      }  in
                    let env' = push_bvs e0 (bv' :: bvs)  in
                    replace_cur
                      (let uu___100_5086 = goal  in
                       {
                         FStar_Tactics_Types.context = env';
                         FStar_Tactics_Types.witness =
                           (uu___100_5086.FStar_Tactics_Types.witness);
                         FStar_Tactics_Types.goal_ty =
                           (uu___100_5086.FStar_Tactics_Types.goal_ty);
                         FStar_Tactics_Types.opts =
                           (uu___100_5086.FStar_Tactics_Types.opts);
                         FStar_Tactics_Types.is_guard =
                           (uu___100_5086.FStar_Tactics_Types.is_guard)
                       })))
  
let (revert : Prims.unit tac) =
  bind cur_goal
    (fun goal  ->
       let uu____5094 =
         FStar_TypeChecker_Env.pop_bv goal.FStar_Tactics_Types.context  in
       match uu____5094 with
       | FStar_Pervasives_Native.None  -> fail "Cannot revert; empty context"
       | FStar_Pervasives_Native.Some (x,env') ->
           let typ' =
             let uu____5116 =
               FStar_Syntax_Syntax.mk_Total goal.FStar_Tactics_Types.goal_ty
                in
             FStar_Syntax_Util.arrow [(x, FStar_Pervasives_Native.None)]
               uu____5116
              in
           let w' =
             FStar_Syntax_Util.abs [(x, FStar_Pervasives_Native.None)]
               goal.FStar_Tactics_Types.witness FStar_Pervasives_Native.None
              in
           replace_cur
             (let uu___101_5150 = goal  in
              {
                FStar_Tactics_Types.context = env';
                FStar_Tactics_Types.witness = w';
                FStar_Tactics_Types.goal_ty = typ';
                FStar_Tactics_Types.opts =
                  (uu___101_5150.FStar_Tactics_Types.opts);
                FStar_Tactics_Types.is_guard =
                  (uu___101_5150.FStar_Tactics_Types.is_guard)
              }))
  
let (free_in :
  FStar_Syntax_Syntax.bv -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun bv  ->
    fun t  ->
      let uu____5157 = FStar_Syntax_Free.names t  in
      FStar_Util.set_mem bv uu____5157
  
let rec (clear : FStar_Syntax_Syntax.binder -> Prims.unit tac) =
  fun b  ->
    let bv = FStar_Pervasives_Native.fst b  in
    bind cur_goal
      (fun goal  ->
         mlog
           (fun uu____5173  ->
              let uu____5174 = FStar_Syntax_Print.binder_to_string b  in
              let uu____5175 =
                let uu____5176 =
                  let uu____5177 =
                    FStar_TypeChecker_Env.all_binders
                      goal.FStar_Tactics_Types.context
                     in
                  FStar_All.pipe_right uu____5177 FStar_List.length  in
                FStar_All.pipe_right uu____5176 FStar_Util.string_of_int  in
              FStar_Util.print2 "Clear of (%s), env has %s binders\n"
                uu____5174 uu____5175)
           (fun uu____5188  ->
              let uu____5189 = split_env bv goal.FStar_Tactics_Types.context
                 in
              match uu____5189 with
              | FStar_Pervasives_Native.None  ->
                  fail "Cannot clear; binder not in environment"
              | FStar_Pervasives_Native.Some (e',bvs) ->
                  let rec check bvs1 =
                    match bvs1 with
                    | [] -> ret ()
                    | bv'::bvs2 ->
                        let uu____5234 =
                          free_in bv bv'.FStar_Syntax_Syntax.sort  in
                        if uu____5234
                        then
                          let uu____5237 =
                            let uu____5238 =
                              FStar_Syntax_Print.bv_to_string bv'  in
                            FStar_Util.format1
                              "Cannot clear; binder present in the type of %s"
                              uu____5238
                             in
                          fail uu____5237
                        else check bvs2
                     in
                  let uu____5240 =
                    free_in bv goal.FStar_Tactics_Types.goal_ty  in
                  if uu____5240
                  then fail "Cannot clear; binder present in goal"
                  else
                    (let uu____5244 = check bvs  in
                     bind uu____5244
                       (fun uu____5250  ->
                          let env' = push_bvs e' bvs  in
                          let uu____5252 =
                            new_uvar "clear.witness" env'
                              goal.FStar_Tactics_Types.goal_ty
                             in
                          bind uu____5252
                            (fun ut  ->
                               let uu____5258 =
                                 do_unify goal.FStar_Tactics_Types.context
                                   goal.FStar_Tactics_Types.witness ut
                                  in
                               bind uu____5258
                                 (fun b1  ->
                                    if b1
                                    then
                                      replace_cur
                                        (let uu___102_5267 = goal  in
                                         {
                                           FStar_Tactics_Types.context = env';
                                           FStar_Tactics_Types.witness = ut;
                                           FStar_Tactics_Types.goal_ty =
                                             (uu___102_5267.FStar_Tactics_Types.goal_ty);
                                           FStar_Tactics_Types.opts =
                                             (uu___102_5267.FStar_Tactics_Types.opts);
                                           FStar_Tactics_Types.is_guard =
                                             (uu___102_5267.FStar_Tactics_Types.is_guard)
                                         })
                                    else
                                      fail
                                        "Cannot clear; binder appears in witness"))))))
  
let (clear_top : Prims.unit tac) =
  bind cur_goal
    (fun goal  ->
       let uu____5276 =
         FStar_TypeChecker_Env.pop_bv goal.FStar_Tactics_Types.context  in
       match uu____5276 with
       | FStar_Pervasives_Native.None  -> fail "Cannot clear; empty context"
       | FStar_Pervasives_Native.Some (x,uu____5290) ->
           let uu____5295 = FStar_Syntax_Syntax.mk_binder x  in
           clear uu____5295)
  
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
           let uu___103_5311 = g  in
           {
             FStar_Tactics_Types.context = ctx';
             FStar_Tactics_Types.witness =
               (uu___103_5311.FStar_Tactics_Types.witness);
             FStar_Tactics_Types.goal_ty =
               (uu___103_5311.FStar_Tactics_Types.goal_ty);
             FStar_Tactics_Types.opts =
               (uu___103_5311.FStar_Tactics_Types.opts);
             FStar_Tactics_Types.is_guard =
               (uu___103_5311.FStar_Tactics_Types.is_guard)
           }  in
         bind dismiss (fun uu____5313  -> add_goals [g']))
  
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
           let uu___104_5329 = g  in
           {
             FStar_Tactics_Types.context = ctx';
             FStar_Tactics_Types.witness =
               (uu___104_5329.FStar_Tactics_Types.witness);
             FStar_Tactics_Types.goal_ty =
               (uu___104_5329.FStar_Tactics_Types.goal_ty);
             FStar_Tactics_Types.opts =
               (uu___104_5329.FStar_Tactics_Types.opts);
             FStar_Tactics_Types.is_guard =
               (uu___104_5329.FStar_Tactics_Types.is_guard)
           }  in
         bind dismiss (fun uu____5331  -> add_goals [g']))
  
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
            let uu____5363 = FStar_Syntax_Subst.compress t  in
            uu____5363.FStar_Syntax_Syntax.n  in
          let uu____5366 =
            if d = FStar_Tactics_Types.TopDown
            then
              f env
                (let uu___106_5372 = t  in
                 {
                   FStar_Syntax_Syntax.n = tn;
                   FStar_Syntax_Syntax.pos =
                     (uu___106_5372.FStar_Syntax_Syntax.pos);
                   FStar_Syntax_Syntax.vars =
                     (uu___106_5372.FStar_Syntax_Syntax.vars)
                 })
            else ret t  in
          bind uu____5366
            (fun t1  ->
               let tn1 =
                 let uu____5380 =
                   let uu____5381 = FStar_Syntax_Subst.compress t1  in
                   uu____5381.FStar_Syntax_Syntax.n  in
                 match uu____5380 with
                 | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
                     let ff = tac_fold_env d f env  in
                     let uu____5413 = ff hd1  in
                     bind uu____5413
                       (fun hd2  ->
                          let fa uu____5433 =
                            match uu____5433 with
                            | (a,q) ->
                                let uu____5446 = ff a  in
                                bind uu____5446 (fun a1  -> ret (a1, q))
                             in
                          let uu____5459 = mapM fa args  in
                          bind uu____5459
                            (fun args1  ->
                               ret (FStar_Syntax_Syntax.Tm_app (hd2, args1))))
                 | FStar_Syntax_Syntax.Tm_abs (bs,t2,k) ->
                     let uu____5519 = FStar_Syntax_Subst.open_term bs t2  in
                     (match uu____5519 with
                      | (bs1,t') ->
                          let uu____5528 =
                            let uu____5531 =
                              FStar_TypeChecker_Env.push_binders env bs1  in
                            tac_fold_env d f uu____5531 t'  in
                          bind uu____5528
                            (fun t''  ->
                               let uu____5535 =
                                 let uu____5536 =
                                   let uu____5553 =
                                     FStar_Syntax_Subst.close_binders bs1  in
                                   let uu____5554 =
                                     FStar_Syntax_Subst.close bs1 t''  in
                                   (uu____5553, uu____5554, k)  in
                                 FStar_Syntax_Syntax.Tm_abs uu____5536  in
                               ret uu____5535))
                 | FStar_Syntax_Syntax.Tm_arrow (bs,k) -> ret tn
                 | uu____5575 -> ret tn  in
               bind tn1
                 (fun tn2  ->
                    let t' =
                      let uu___105_5582 = t1  in
                      {
                        FStar_Syntax_Syntax.n = tn2;
                        FStar_Syntax_Syntax.pos =
                          (uu___105_5582.FStar_Syntax_Syntax.pos);
                        FStar_Syntax_Syntax.vars =
                          (uu___105_5582.FStar_Syntax_Syntax.vars)
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
            let uu____5611 = FStar_TypeChecker_TcTerm.tc_term env t  in
            match uu____5611 with
            | (t1,lcomp,g) ->
                let uu____5623 =
                  (let uu____5626 =
                     FStar_Syntax_Util.is_pure_or_ghost_lcomp lcomp  in
                   Prims.op_Negation uu____5626) ||
                    (let uu____5628 = FStar_TypeChecker_Rel.is_trivial g  in
                     Prims.op_Negation uu____5628)
                   in
                if uu____5623
                then ret t1
                else
                  (let rewrite_eq =
                     let typ = lcomp.FStar_Syntax_Syntax.res_typ  in
                     let uu____5638 = new_uvar "pointwise_rec" env typ  in
                     bind uu____5638
                       (fun ut  ->
                          log ps
                            (fun uu____5649  ->
                               let uu____5650 =
                                 FStar_Syntax_Print.term_to_string t1  in
                               let uu____5651 =
                                 FStar_Syntax_Print.term_to_string ut  in
                               FStar_Util.print2
                                 "Pointwise_rec: making equality\n\t%s ==\n\t%s\n"
                                 uu____5650 uu____5651);
                          (let uu____5652 =
                             let uu____5655 =
                               let uu____5656 =
                                 FStar_TypeChecker_TcTerm.universe_of env typ
                                  in
                               FStar_Syntax_Util.mk_eq2 uu____5656 typ t1 ut
                                in
                             add_irrelevant_goal "pointwise_rec equation" env
                               uu____5655 opts
                              in
                           bind uu____5652
                             (fun uu____5659  ->
                                let uu____5660 =
                                  bind tau
                                    (fun uu____5666  ->
                                       let ut1 =
                                         FStar_TypeChecker_Normalize.reduce_uvar_solutions
                                           env ut
                                          in
                                       log ps
                                         (fun uu____5672  ->
                                            let uu____5673 =
                                              FStar_Syntax_Print.term_to_string
                                                t1
                                               in
                                            let uu____5674 =
                                              FStar_Syntax_Print.term_to_string
                                                ut1
                                               in
                                            FStar_Util.print2
                                              "Pointwise_rec: succeeded rewriting\n\t%s to\n\t%s\n"
                                              uu____5673 uu____5674);
                                       ret ut1)
                                   in
                                focus uu____5660)))
                      in
                   let uu____5675 = trytac' rewrite_eq  in
                   bind uu____5675
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
          let uu____5823 = FStar_Syntax_Subst.compress t  in
          maybe_continue ctrl uu____5823
            (fun t1  ->
               let uu____5827 =
                 f env
                   (let uu___109_5836 = t1  in
                    {
                      FStar_Syntax_Syntax.n = (t1.FStar_Syntax_Syntax.n);
                      FStar_Syntax_Syntax.pos =
                        (uu___109_5836.FStar_Syntax_Syntax.pos);
                      FStar_Syntax_Syntax.vars =
                        (uu___109_5836.FStar_Syntax_Syntax.vars)
                    })
                  in
               bind uu____5827
                 (fun uu____5848  ->
                    match uu____5848 with
                    | (t2,ctrl1) ->
                        maybe_continue ctrl1 t2
                          (fun t3  ->
                             let uu____5867 =
                               let uu____5868 =
                                 FStar_Syntax_Subst.compress t3  in
                               uu____5868.FStar_Syntax_Syntax.n  in
                             match uu____5867 with
                             | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
                                 let uu____5901 =
                                   ctrl_tac_fold f env ctrl1 hd1  in
                                 bind uu____5901
                                   (fun uu____5926  ->
                                      match uu____5926 with
                                      | (hd2,ctrl2) ->
                                          let ctrl3 = keep_going ctrl2  in
                                          let uu____5942 =
                                            ctrl_tac_fold_args f env ctrl3
                                              args
                                             in
                                          bind uu____5942
                                            (fun uu____5969  ->
                                               match uu____5969 with
                                               | (args1,ctrl4) ->
                                                   ret
                                                     ((let uu___107_5999 = t3
                                                          in
                                                       {
                                                         FStar_Syntax_Syntax.n
                                                           =
                                                           (FStar_Syntax_Syntax.Tm_app
                                                              (hd2, args1));
                                                         FStar_Syntax_Syntax.pos
                                                           =
                                                           (uu___107_5999.FStar_Syntax_Syntax.pos);
                                                         FStar_Syntax_Syntax.vars
                                                           =
                                                           (uu___107_5999.FStar_Syntax_Syntax.vars)
                                                       }), ctrl4)))
                             | FStar_Syntax_Syntax.Tm_abs (bs,t4,k) ->
                                 let uu____6025 =
                                   FStar_Syntax_Subst.open_term bs t4  in
                                 (match uu____6025 with
                                  | (bs1,t') ->
                                      let uu____6040 =
                                        let uu____6047 =
                                          FStar_TypeChecker_Env.push_binders
                                            env bs1
                                           in
                                        ctrl_tac_fold f uu____6047 ctrl1 t'
                                         in
                                      bind uu____6040
                                        (fun uu____6065  ->
                                           match uu____6065 with
                                           | (t'',ctrl2) ->
                                               let uu____6080 =
                                                 let uu____6087 =
                                                   let uu___108_6090 = t4  in
                                                   let uu____6093 =
                                                     let uu____6094 =
                                                       let uu____6111 =
                                                         FStar_Syntax_Subst.close_binders
                                                           bs1
                                                          in
                                                       let uu____6112 =
                                                         FStar_Syntax_Subst.close
                                                           bs1 t''
                                                          in
                                                       (uu____6111,
                                                         uu____6112, k)
                                                        in
                                                     FStar_Syntax_Syntax.Tm_abs
                                                       uu____6094
                                                      in
                                                   {
                                                     FStar_Syntax_Syntax.n =
                                                       uu____6093;
                                                     FStar_Syntax_Syntax.pos
                                                       =
                                                       (uu___108_6090.FStar_Syntax_Syntax.pos);
                                                     FStar_Syntax_Syntax.vars
                                                       =
                                                       (uu___108_6090.FStar_Syntax_Syntax.vars)
                                                   }  in
                                                 (uu____6087, ctrl2)  in
                                               ret uu____6080))
                             | FStar_Syntax_Syntax.Tm_arrow (bs,k) ->
                                 ret (t3, ctrl1)
                             | uu____6145 -> ret (t3, ctrl1))))

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
              let uu____6196 = ctrl_tac_fold f env ctrl t  in
              bind uu____6196
                (fun uu____6224  ->
                   match uu____6224 with
                   | (t1,ctrl1) ->
                       let uu____6243 = ctrl_tac_fold_args f env ctrl1 ts1
                          in
                       bind uu____6243
                         (fun uu____6274  ->
                            match uu____6274 with
                            | (ts2,ctrl2) -> ret (((t1, q) :: ts2), ctrl2)))

let (rewrite_rec :
  FStar_Tactics_Types.proofstate ->
    (FStar_Syntax_Syntax.term -> rewrite_result ctrl_tac) ->
      Prims.unit tac ->
        FStar_Options.optionstate ->
          FStar_TypeChecker_Env.env ->
            FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term ctrl_tac)
  =
  fun ps  ->
    fun ctrl  ->
      fun rewriter  ->
        fun opts  ->
          fun env  ->
            fun t  ->
              let t1 = FStar_Syntax_Subst.compress t  in
              let uu____6358 =
                let uu____6365 =
                  add_irrelevant_goal "dummy" env FStar_Syntax_Util.t_true
                    opts
                   in
                bind uu____6365
                  (fun uu____6374  ->
                     let uu____6375 = ctrl t1  in
                     bind uu____6375
                       (fun res  -> bind trivial (fun uu____6402  -> ret res)))
                 in
              bind uu____6358
                (fun uu____6418  ->
                   match uu____6418 with
                   | (should_rewrite,ctrl1) ->
                       if Prims.op_Negation should_rewrite
                       then ret (t1, ctrl1)
                       else
                         (let uu____6442 =
                            FStar_TypeChecker_TcTerm.tc_term env t1  in
                          match uu____6442 with
                          | (t2,lcomp,g) ->
                              let uu____6458 =
                                (let uu____6461 =
                                   FStar_Syntax_Util.is_pure_or_ghost_lcomp
                                     lcomp
                                    in
                                 Prims.op_Negation uu____6461) ||
                                  (let uu____6463 =
                                     FStar_TypeChecker_Rel.is_trivial g  in
                                   Prims.op_Negation uu____6463)
                                 in
                              if uu____6458
                              then ret (t2, globalStop)
                              else
                                (let typ = lcomp.FStar_Syntax_Syntax.res_typ
                                    in
                                 let uu____6478 =
                                   new_uvar "pointwise_rec" env typ  in
                                 bind uu____6478
                                   (fun ut  ->
                                      log ps
                                        (fun uu____6493  ->
                                           let uu____6494 =
                                             FStar_Syntax_Print.term_to_string
                                               t2
                                              in
                                           let uu____6495 =
                                             FStar_Syntax_Print.term_to_string
                                               ut
                                              in
                                           FStar_Util.print2
                                             "Pointwise_rec: making equality\n\t%s ==\n\t%s\n"
                                             uu____6494 uu____6495);
                                      (let uu____6496 =
                                         let uu____6499 =
                                           let uu____6500 =
                                             FStar_TypeChecker_TcTerm.universe_of
                                               env typ
                                              in
                                           FStar_Syntax_Util.mk_eq2
                                             uu____6500 typ t2 ut
                                            in
                                         add_irrelevant_goal
                                           "rewrite_rec equation" env
                                           uu____6499 opts
                                          in
                                       bind uu____6496
                                         (fun uu____6507  ->
                                            let uu____6508 =
                                              bind rewriter
                                                (fun uu____6522  ->
                                                   let ut1 =
                                                     FStar_TypeChecker_Normalize.reduce_uvar_solutions
                                                       env ut
                                                      in
                                                   log ps
                                                     (fun uu____6528  ->
                                                        let uu____6529 =
                                                          FStar_Syntax_Print.term_to_string
                                                            t2
                                                           in
                                                        let uu____6530 =
                                                          FStar_Syntax_Print.term_to_string
                                                            ut1
                                                           in
                                                        FStar_Util.print2
                                                          "rewrite_rec: succeeded rewriting\n\t%s to\n\t%s\n"
                                                          uu____6529
                                                          uu____6530);
                                                   ret (ut1, ctrl1))
                                               in
                                            focus uu____6508))))))
  
let (topdown_rewrite :
  (FStar_Syntax_Syntax.term ->
     (Prims.bool,FStar_BigInt.t) FStar_Pervasives_Native.tuple2 tac)
    -> Prims.unit tac -> Prims.unit tac)
  =
  fun ctrl  ->
    fun rewriter  ->
      bind get
        (fun ps  ->
           let uu____6574 =
             match ps.FStar_Tactics_Types.goals with
             | g::gs -> (g, gs)
             | [] -> failwith "Pointwise: no goals"  in
           match uu____6574 with
           | (g,gs) ->
               let gt1 = g.FStar_Tactics_Types.goal_ty  in
               (log ps
                  (fun uu____6611  ->
                     let uu____6612 = FStar_Syntax_Print.term_to_string gt1
                        in
                     FStar_Util.print1 "Pointwise starting with %s\n"
                       uu____6612);
                bind dismiss_all
                  (fun uu____6615  ->
                     let uu____6616 =
                       ctrl_tac_fold
                         (rewrite_rec ps ctrl rewriter
                            g.FStar_Tactics_Types.opts)
                         g.FStar_Tactics_Types.context keepGoing gt1
                        in
                     bind uu____6616
                       (fun uu____6634  ->
                          match uu____6634 with
                          | (gt',uu____6642) ->
                              (log ps
                                 (fun uu____6646  ->
                                    let uu____6647 =
                                      FStar_Syntax_Print.term_to_string gt'
                                       in
                                    FStar_Util.print1
                                      "Pointwise seems to have succeded with %s\n"
                                      uu____6647);
                               (let uu____6648 = push_goals gs  in
                                bind uu____6648
                                  (fun uu____6652  ->
                                     add_goals
                                       [(let uu___110_6654 = g  in
                                         {
                                           FStar_Tactics_Types.context =
                                             (uu___110_6654.FStar_Tactics_Types.context);
                                           FStar_Tactics_Types.witness =
                                             (uu___110_6654.FStar_Tactics_Types.witness);
                                           FStar_Tactics_Types.goal_ty = gt';
                                           FStar_Tactics_Types.opts =
                                             (uu___110_6654.FStar_Tactics_Types.opts);
                                           FStar_Tactics_Types.is_guard =
                                             (uu___110_6654.FStar_Tactics_Types.is_guard)
                                         })])))))))
  
let (pointwise :
  FStar_Tactics_Types.direction -> Prims.unit tac -> Prims.unit tac) =
  fun d  ->
    fun tau  ->
      bind get
        (fun ps  ->
           let uu____6676 =
             match ps.FStar_Tactics_Types.goals with
             | g::gs -> (g, gs)
             | [] -> failwith "Pointwise: no goals"  in
           match uu____6676 with
           | (g,gs) ->
               let gt1 = g.FStar_Tactics_Types.goal_ty  in
               (log ps
                  (fun uu____6713  ->
                     let uu____6714 = FStar_Syntax_Print.term_to_string gt1
                        in
                     FStar_Util.print1 "Pointwise starting with %s\n"
                       uu____6714);
                bind dismiss_all
                  (fun uu____6717  ->
                     let uu____6718 =
                       tac_fold_env d
                         (pointwise_rec ps tau g.FStar_Tactics_Types.opts)
                         g.FStar_Tactics_Types.context gt1
                        in
                     bind uu____6718
                       (fun gt'  ->
                          log ps
                            (fun uu____6728  ->
                               let uu____6729 =
                                 FStar_Syntax_Print.term_to_string gt'  in
                               FStar_Util.print1
                                 "Pointwise seems to have succeded with %s\n"
                                 uu____6729);
                          (let uu____6730 = push_goals gs  in
                           bind uu____6730
                             (fun uu____6734  ->
                                add_goals
                                  [(let uu___111_6736 = g  in
                                    {
                                      FStar_Tactics_Types.context =
                                        (uu___111_6736.FStar_Tactics_Types.context);
                                      FStar_Tactics_Types.witness =
                                        (uu___111_6736.FStar_Tactics_Types.witness);
                                      FStar_Tactics_Types.goal_ty = gt';
                                      FStar_Tactics_Types.opts =
                                        (uu___111_6736.FStar_Tactics_Types.opts);
                                      FStar_Tactics_Types.is_guard =
                                        (uu___111_6736.FStar_Tactics_Types.is_guard)
                                    })]))))))
  
let (trefl : Prims.unit tac) =
  bind cur_goal
    (fun g  ->
       let uu____6756 =
         FStar_Syntax_Util.un_squash g.FStar_Tactics_Types.goal_ty  in
       match uu____6756 with
       | FStar_Pervasives_Native.Some t ->
           let uu____6768 = FStar_Syntax_Util.head_and_args' t  in
           (match uu____6768 with
            | (hd1,args) ->
                let uu____6801 =
                  let uu____6814 =
                    let uu____6815 = FStar_Syntax_Util.un_uinst hd1  in
                    uu____6815.FStar_Syntax_Syntax.n  in
                  (uu____6814, args)  in
                (match uu____6801 with
                 | (FStar_Syntax_Syntax.Tm_fvar
                    fv,uu____6829::(l,uu____6831)::(r,uu____6833)::[]) when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.eq2_lid
                     ->
                     let uu____6880 =
                       do_unify g.FStar_Tactics_Types.context l r  in
                     bind uu____6880
                       (fun b  ->
                          if Prims.op_Negation b
                          then
                            let uu____6889 =
                              tts g.FStar_Tactics_Types.context l  in
                            let uu____6890 =
                              tts g.FStar_Tactics_Types.context r  in
                            fail2 "trefl: not a trivial equality (%s vs %s)"
                              uu____6889 uu____6890
                          else solve g FStar_Syntax_Util.exp_unit)
                 | (hd2,uu____6893) ->
                     let uu____6910 = tts g.FStar_Tactics_Types.context t  in
                     fail1 "trefl: not an equality (%s)" uu____6910))
       | FStar_Pervasives_Native.None  -> fail "not an irrelevant goal")
  
let (dup : Prims.unit tac) =
  bind cur_goal
    (fun g  ->
       let uu____6920 =
         new_uvar "dup" g.FStar_Tactics_Types.context
           g.FStar_Tactics_Types.goal_ty
          in
       bind uu____6920
         (fun u  ->
            let g' =
              let uu___112_6927 = g  in
              {
                FStar_Tactics_Types.context =
                  (uu___112_6927.FStar_Tactics_Types.context);
                FStar_Tactics_Types.witness = u;
                FStar_Tactics_Types.goal_ty =
                  (uu___112_6927.FStar_Tactics_Types.goal_ty);
                FStar_Tactics_Types.opts =
                  (uu___112_6927.FStar_Tactics_Types.opts);
                FStar_Tactics_Types.is_guard =
                  (uu___112_6927.FStar_Tactics_Types.is_guard)
              }  in
            bind dismiss
              (fun uu____6930  ->
                 let uu____6931 =
                   let uu____6934 =
                     let uu____6935 =
                       FStar_TypeChecker_TcTerm.universe_of
                         g.FStar_Tactics_Types.context
                         g.FStar_Tactics_Types.goal_ty
                        in
                     FStar_Syntax_Util.mk_eq2 uu____6935
                       g.FStar_Tactics_Types.goal_ty u
                       g.FStar_Tactics_Types.witness
                      in
                   add_irrelevant_goal "dup equation"
                     g.FStar_Tactics_Types.context uu____6934
                     g.FStar_Tactics_Types.opts
                    in
                 bind uu____6931
                   (fun uu____6938  ->
                      let uu____6939 = add_goals [g']  in
                      bind uu____6939 (fun uu____6943  -> ret ())))))
  
let (flip : Prims.unit tac) =
  bind get
    (fun ps  ->
       match ps.FStar_Tactics_Types.goals with
       | g1::g2::gs ->
           set
             (let uu___113_6962 = ps  in
              {
                FStar_Tactics_Types.main_context =
                  (uu___113_6962.FStar_Tactics_Types.main_context);
                FStar_Tactics_Types.main_goal =
                  (uu___113_6962.FStar_Tactics_Types.main_goal);
                FStar_Tactics_Types.all_implicits =
                  (uu___113_6962.FStar_Tactics_Types.all_implicits);
                FStar_Tactics_Types.goals = (g2 :: g1 :: gs);
                FStar_Tactics_Types.smt_goals =
                  (uu___113_6962.FStar_Tactics_Types.smt_goals);
                FStar_Tactics_Types.depth =
                  (uu___113_6962.FStar_Tactics_Types.depth);
                FStar_Tactics_Types.__dump =
                  (uu___113_6962.FStar_Tactics_Types.__dump);
                FStar_Tactics_Types.psc =
                  (uu___113_6962.FStar_Tactics_Types.psc);
                FStar_Tactics_Types.entry_range =
                  (uu___113_6962.FStar_Tactics_Types.entry_range);
                FStar_Tactics_Types.guard_policy =
                  (uu___113_6962.FStar_Tactics_Types.guard_policy)
              })
       | uu____6963 -> fail "flip: less than 2 goals")
  
let (later : Prims.unit tac) =
  bind get
    (fun ps  ->
       match ps.FStar_Tactics_Types.goals with
       | [] -> ret ()
       | g::gs ->
           set
             (let uu___114_6980 = ps  in
              {
                FStar_Tactics_Types.main_context =
                  (uu___114_6980.FStar_Tactics_Types.main_context);
                FStar_Tactics_Types.main_goal =
                  (uu___114_6980.FStar_Tactics_Types.main_goal);
                FStar_Tactics_Types.all_implicits =
                  (uu___114_6980.FStar_Tactics_Types.all_implicits);
                FStar_Tactics_Types.goals = (FStar_List.append gs [g]);
                FStar_Tactics_Types.smt_goals =
                  (uu___114_6980.FStar_Tactics_Types.smt_goals);
                FStar_Tactics_Types.depth =
                  (uu___114_6980.FStar_Tactics_Types.depth);
                FStar_Tactics_Types.__dump =
                  (uu___114_6980.FStar_Tactics_Types.__dump);
                FStar_Tactics_Types.psc =
                  (uu___114_6980.FStar_Tactics_Types.psc);
                FStar_Tactics_Types.entry_range =
                  (uu___114_6980.FStar_Tactics_Types.entry_range);
                FStar_Tactics_Types.guard_policy =
                  (uu___114_6980.FStar_Tactics_Types.guard_policy)
              }))
  
let (qed : Prims.unit tac) =
  bind get
    (fun ps  ->
       match ps.FStar_Tactics_Types.goals with
       | [] -> ret ()
       | uu____6989 -> fail "Not done!")
  
let (cases :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 tac)
  =
  fun t  ->
    let uu____7007 =
      bind cur_goal
        (fun g  ->
           let uu____7021 = __tc g.FStar_Tactics_Types.context t  in
           bind uu____7021
             (fun uu____7057  ->
                match uu____7057 with
                | (t1,typ,guard) ->
                    let uu____7073 = FStar_Syntax_Util.head_and_args typ  in
                    (match uu____7073 with
                     | (hd1,args) ->
                         let uu____7116 =
                           let uu____7129 =
                             let uu____7130 = FStar_Syntax_Util.un_uinst hd1
                                in
                             uu____7130.FStar_Syntax_Syntax.n  in
                           (uu____7129, args)  in
                         (match uu____7116 with
                          | (FStar_Syntax_Syntax.Tm_fvar
                             fv,(p,uu____7149)::(q,uu____7151)::[]) when
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
                                let uu___115_7189 = g  in
                                let uu____7190 =
                                  FStar_TypeChecker_Env.push_bv
                                    g.FStar_Tactics_Types.context v_p
                                   in
                                {
                                  FStar_Tactics_Types.context = uu____7190;
                                  FStar_Tactics_Types.witness =
                                    (uu___115_7189.FStar_Tactics_Types.witness);
                                  FStar_Tactics_Types.goal_ty =
                                    (uu___115_7189.FStar_Tactics_Types.goal_ty);
                                  FStar_Tactics_Types.opts =
                                    (uu___115_7189.FStar_Tactics_Types.opts);
                                  FStar_Tactics_Types.is_guard =
                                    (uu___115_7189.FStar_Tactics_Types.is_guard)
                                }  in
                              let g2 =
                                let uu___116_7192 = g  in
                                let uu____7193 =
                                  FStar_TypeChecker_Env.push_bv
                                    g.FStar_Tactics_Types.context v_q
                                   in
                                {
                                  FStar_Tactics_Types.context = uu____7193;
                                  FStar_Tactics_Types.witness =
                                    (uu___116_7192.FStar_Tactics_Types.witness);
                                  FStar_Tactics_Types.goal_ty =
                                    (uu___116_7192.FStar_Tactics_Types.goal_ty);
                                  FStar_Tactics_Types.opts =
                                    (uu___116_7192.FStar_Tactics_Types.opts);
                                  FStar_Tactics_Types.is_guard =
                                    (uu___116_7192.FStar_Tactics_Types.is_guard)
                                }  in
                              bind dismiss
                                (fun uu____7200  ->
                                   let uu____7201 = add_goals [g1; g2]  in
                                   bind uu____7201
                                     (fun uu____7210  ->
                                        let uu____7211 =
                                          let uu____7216 =
                                            FStar_Syntax_Syntax.bv_to_name
                                              v_p
                                             in
                                          let uu____7217 =
                                            FStar_Syntax_Syntax.bv_to_name
                                              v_q
                                             in
                                          (uu____7216, uu____7217)  in
                                        ret uu____7211))
                          | uu____7222 ->
                              let uu____7235 =
                                tts g.FStar_Tactics_Types.context typ  in
                              fail1 "Not a disjunction: %s" uu____7235))))
       in
    FStar_All.pipe_left (wrap_err "cases") uu____7007
  
let (set_options : Prims.string -> Prims.unit tac) =
  fun s  ->
    bind cur_goal
      (fun g  ->
         FStar_Options.push ();
         (let uu____7273 = FStar_Util.smap_copy g.FStar_Tactics_Types.opts
             in
          FStar_Options.set uu____7273);
         (let res = FStar_Options.set_options FStar_Options.Set s  in
          let opts' = FStar_Options.peek ()  in
          FStar_Options.pop ();
          (match res with
           | FStar_Getopt.Success  ->
               let g' =
                 let uu___117_7280 = g  in
                 {
                   FStar_Tactics_Types.context =
                     (uu___117_7280.FStar_Tactics_Types.context);
                   FStar_Tactics_Types.witness =
                     (uu___117_7280.FStar_Tactics_Types.witness);
                   FStar_Tactics_Types.goal_ty =
                     (uu___117_7280.FStar_Tactics_Types.goal_ty);
                   FStar_Tactics_Types.opts = opts';
                   FStar_Tactics_Types.is_guard =
                     (uu___117_7280.FStar_Tactics_Types.is_guard)
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
      let uu____7324 =
        bind cur_goal
          (fun goal  ->
             let env =
               FStar_TypeChecker_Env.set_expected_typ
                 goal.FStar_Tactics_Types.context ty
                in
             let uu____7332 = __tc env tm  in
             bind uu____7332
               (fun uu____7352  ->
                  match uu____7352 with
                  | (tm1,typ,guard) ->
                      let uu____7364 =
                        proc_guard "unquote" env guard
                          goal.FStar_Tactics_Types.opts
                         in
                      bind uu____7364 (fun uu____7368  -> ret tm1)))
         in
      FStar_All.pipe_left (wrap_err "unquote") uu____7324
  
let (uvar_env :
  env ->
    FStar_Syntax_Syntax.typ FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.term tac)
  =
  fun env  ->
    fun ty  ->
      let uu____7387 =
        match ty with
        | FStar_Pervasives_Native.Some ty1 -> ret ty1
        | FStar_Pervasives_Native.None  ->
            let uu____7393 =
              let uu____7394 = FStar_Syntax_Util.type_u ()  in
              FStar_All.pipe_left FStar_Pervasives_Native.fst uu____7394  in
            new_uvar "uvar_env.2" env uu____7393
         in
      bind uu____7387
        (fun typ  ->
           let uu____7406 = new_uvar "uvar_env" env typ  in
           bind uu____7406 (fun t  -> ret t))
  
let (unshelve : FStar_Syntax_Syntax.term -> Prims.unit tac) =
  fun t  ->
    let uu____7418 =
      bind cur_goal
        (fun goal  ->
           let uu____7424 = __tc goal.FStar_Tactics_Types.context t  in
           bind uu____7424
             (fun uu____7444  ->
                match uu____7444 with
                | (t1,typ,guard) ->
                    let uu____7456 =
                      proc_guard "unshelve" goal.FStar_Tactics_Types.context
                        guard goal.FStar_Tactics_Types.opts
                       in
                    bind uu____7456
                      (fun uu____7461  ->
                         let uu____7462 =
                           let uu____7465 =
                             let uu___118_7466 = goal  in
                             let uu____7467 =
                               bnorm goal.FStar_Tactics_Types.context t1  in
                             let uu____7468 =
                               bnorm goal.FStar_Tactics_Types.context typ  in
                             {
                               FStar_Tactics_Types.context =
                                 (uu___118_7466.FStar_Tactics_Types.context);
                               FStar_Tactics_Types.witness = uu____7467;
                               FStar_Tactics_Types.goal_ty = uu____7468;
                               FStar_Tactics_Types.opts =
                                 (uu___118_7466.FStar_Tactics_Types.opts);
                               FStar_Tactics_Types.is_guard = false
                             }  in
                           [uu____7465]  in
                         add_goals uu____7462)))
       in
    FStar_All.pipe_left (wrap_err "unshelve") uu____7418
  
let (unify :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool tac) =
  fun t1  ->
    fun t2  ->
      bind get
        (fun ps  -> do_unify ps.FStar_Tactics_Types.main_context t1 t2)
  
let (launch_process :
  Prims.string -> Prims.string -> Prims.string -> Prims.string tac) =
  fun prog  ->
    fun args  ->
      fun input  ->
        bind idtac
          (fun uu____7501  ->
             let uu____7502 = FStar_Options.unsafe_tactic_exec ()  in
             if uu____7502
             then
               let s =
                 FStar_Util.launch_process true "tactic_launch" prog args
                   input (fun uu____7508  -> fun uu____7509  -> false)
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
        (fun uu____7523  ->
           let uu____7524 =
             FStar_Syntax_Syntax.gen_bv nm FStar_Pervasives_Native.None t  in
           ret uu____7524)
  
let (change : FStar_Syntax_Syntax.typ -> Prims.unit tac) =
  fun ty  ->
    let uu____7532 =
      mlog
        (fun uu____7537  ->
           let uu____7538 = FStar_Syntax_Print.term_to_string ty  in
           FStar_Util.print1 "change: ty = %s\n" uu____7538)
        (fun uu____7540  ->
           bind cur_goal
             (fun g  ->
                let uu____7544 = __tc g.FStar_Tactics_Types.context ty  in
                bind uu____7544
                  (fun uu____7564  ->
                     match uu____7564 with
                     | (ty1,uu____7574,guard) ->
                         let uu____7576 =
                           proc_guard "change" g.FStar_Tactics_Types.context
                             guard g.FStar_Tactics_Types.opts
                            in
                         bind uu____7576
                           (fun uu____7581  ->
                              let uu____7582 =
                                do_unify g.FStar_Tactics_Types.context
                                  g.FStar_Tactics_Types.goal_ty ty1
                                 in
                              bind uu____7582
                                (fun bb  ->
                                   if bb
                                   then
                                     replace_cur
                                       (let uu___119_7591 = g  in
                                        {
                                          FStar_Tactics_Types.context =
                                            (uu___119_7591.FStar_Tactics_Types.context);
                                          FStar_Tactics_Types.witness =
                                            (uu___119_7591.FStar_Tactics_Types.witness);
                                          FStar_Tactics_Types.goal_ty = ty1;
                                          FStar_Tactics_Types.opts =
                                            (uu___119_7591.FStar_Tactics_Types.opts);
                                          FStar_Tactics_Types.is_guard =
                                            (uu___119_7591.FStar_Tactics_Types.is_guard)
                                        })
                                   else
                                     (let steps =
                                        [FStar_TypeChecker_Normalize.Reify;
                                        FStar_TypeChecker_Normalize.UnfoldUntil
                                          FStar_Syntax_Syntax.Delta_constant;
                                        FStar_TypeChecker_Normalize.AllowUnboundUniverses;
                                        FStar_TypeChecker_Normalize.Primops;
                                        FStar_TypeChecker_Normalize.Simplify;
                                        FStar_TypeChecker_Normalize.UnfoldTac;
                                        FStar_TypeChecker_Normalize.Unmeta]
                                         in
                                      let ng =
                                        normalize steps
                                          g.FStar_Tactics_Types.context
                                          g.FStar_Tactics_Types.goal_ty
                                         in
                                      let nty =
                                        normalize steps
                                          g.FStar_Tactics_Types.context ty1
                                         in
                                      let uu____7598 =
                                        do_unify
                                          g.FStar_Tactics_Types.context ng
                                          nty
                                         in
                                      bind uu____7598
                                        (fun b  ->
                                           if b
                                           then
                                             replace_cur
                                               (let uu___120_7607 = g  in
                                                {
                                                  FStar_Tactics_Types.context
                                                    =
                                                    (uu___120_7607.FStar_Tactics_Types.context);
                                                  FStar_Tactics_Types.witness
                                                    =
                                                    (uu___120_7607.FStar_Tactics_Types.witness);
                                                  FStar_Tactics_Types.goal_ty
                                                    = ty1;
                                                  FStar_Tactics_Types.opts =
                                                    (uu___120_7607.FStar_Tactics_Types.opts);
                                                  FStar_Tactics_Types.is_guard
                                                    =
                                                    (uu___120_7607.FStar_Tactics_Types.is_guard)
                                                })
                                           else fail "not convertible")))))))
       in
    FStar_All.pipe_left (wrap_err "change") uu____7532
  
let (goal_of_goal_ty :
  env ->
    FStar_Syntax_Syntax.typ ->
      (FStar_Tactics_Types.goal,FStar_TypeChecker_Env.guard_t)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun typ  ->
      let uu____7627 =
        FStar_TypeChecker_Util.new_implicit_var "proofstate_of_goal_ty"
          typ.FStar_Syntax_Syntax.pos env typ
         in
      match uu____7627 with
      | (u,uu____7645,g_u) ->
          let g =
            let uu____7660 = FStar_Options.peek ()  in
            {
              FStar_Tactics_Types.context = env;
              FStar_Tactics_Types.witness = u;
              FStar_Tactics_Types.goal_ty = typ;
              FStar_Tactics_Types.opts = uu____7660;
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
      let uu____7671 = goal_of_goal_ty env typ  in
      match uu____7671 with
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
              FStar_Tactics_Types.entry_range = FStar_Range.dummyRange;
              FStar_Tactics_Types.guard_policy = FStar_Tactics_Types.SMT
            }  in
          (ps, (g.FStar_Tactics_Types.witness))
  