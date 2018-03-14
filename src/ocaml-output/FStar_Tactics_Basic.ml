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
let (__do_unify :
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
  
let (do_unify :
  env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool tac)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____1067 = __do_unify env t1 t2  in
        bind uu____1067
          (fun b  ->
             if Prims.op_Negation b
             then
               let t11 = FStar_TypeChecker_Normalize.normalize [] env t1  in
               let t21 = FStar_TypeChecker_Normalize.normalize [] env t2  in
               __do_unify env t11 t21
             else ret b)
  
let (trysolve :
  FStar_Tactics_Types.goal -> FStar_Syntax_Syntax.term -> Prims.bool tac) =
  fun goal  ->
    fun solution  ->
      do_unify goal.FStar_Tactics_Types.context solution
        goal.FStar_Tactics_Types.witness
  
let (__dismiss : Prims.unit tac) =
  bind get
    (fun p  ->
       let uu____1094 =
         let uu___63_1095 = p  in
         let uu____1096 = FStar_List.tl p.FStar_Tactics_Types.goals  in
         {
           FStar_Tactics_Types.main_context =
             (uu___63_1095.FStar_Tactics_Types.main_context);
           FStar_Tactics_Types.main_goal =
             (uu___63_1095.FStar_Tactics_Types.main_goal);
           FStar_Tactics_Types.all_implicits =
             (uu___63_1095.FStar_Tactics_Types.all_implicits);
           FStar_Tactics_Types.goals = uu____1096;
           FStar_Tactics_Types.smt_goals =
             (uu___63_1095.FStar_Tactics_Types.smt_goals);
           FStar_Tactics_Types.depth =
             (uu___63_1095.FStar_Tactics_Types.depth);
           FStar_Tactics_Types.__dump =
             (uu___63_1095.FStar_Tactics_Types.__dump);
           FStar_Tactics_Types.psc = (uu___63_1095.FStar_Tactics_Types.psc);
           FStar_Tactics_Types.entry_range =
             (uu___63_1095.FStar_Tactics_Types.entry_range);
           FStar_Tactics_Types.guard_policy =
             (uu___63_1095.FStar_Tactics_Types.guard_policy)
         }  in
       set uu____1094)
  
let (dismiss : Prims.unit tac) =
  bind get
    (fun p  ->
       match p.FStar_Tactics_Types.goals with
       | [] -> fail "dismiss: no more goals"
       | uu____1107 -> __dismiss)
  
let (solve :
  FStar_Tactics_Types.goal -> FStar_Syntax_Syntax.term -> Prims.unit tac) =
  fun goal  ->
    fun solution  ->
      let uu____1120 = trysolve goal solution  in
      bind uu____1120
        (fun b  ->
           if b
           then __dismiss
           else
             (let uu____1128 =
                let uu____1129 =
                  tts goal.FStar_Tactics_Types.context solution  in
                let uu____1130 =
                  tts goal.FStar_Tactics_Types.context
                    goal.FStar_Tactics_Types.witness
                   in
                let uu____1131 =
                  tts goal.FStar_Tactics_Types.context
                    goal.FStar_Tactics_Types.goal_ty
                   in
                FStar_Util.format3 "%s does not solve %s : %s" uu____1129
                  uu____1130 uu____1131
                 in
              fail uu____1128))
  
let (dismiss_all : Prims.unit tac) =
  bind get
    (fun p  ->
       set
         (let uu___64_1138 = p  in
          {
            FStar_Tactics_Types.main_context =
              (uu___64_1138.FStar_Tactics_Types.main_context);
            FStar_Tactics_Types.main_goal =
              (uu___64_1138.FStar_Tactics_Types.main_goal);
            FStar_Tactics_Types.all_implicits =
              (uu___64_1138.FStar_Tactics_Types.all_implicits);
            FStar_Tactics_Types.goals = [];
            FStar_Tactics_Types.smt_goals =
              (uu___64_1138.FStar_Tactics_Types.smt_goals);
            FStar_Tactics_Types.depth =
              (uu___64_1138.FStar_Tactics_Types.depth);
            FStar_Tactics_Types.__dump =
              (uu___64_1138.FStar_Tactics_Types.__dump);
            FStar_Tactics_Types.psc = (uu___64_1138.FStar_Tactics_Types.psc);
            FStar_Tactics_Types.entry_range =
              (uu___64_1138.FStar_Tactics_Types.entry_range);
            FStar_Tactics_Types.guard_policy =
              (uu___64_1138.FStar_Tactics_Types.guard_policy)
          }))
  
let (nwarn : Prims.int FStar_ST.ref) =
  FStar_Util.mk_ref (Prims.parse_int "0") 
let (check_valid_goal : FStar_Tactics_Types.goal -> Prims.unit) =
  fun g  ->
    let uu____1155 = FStar_Options.defensive ()  in
    if uu____1155
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
        let uu____1167 = FStar_TypeChecker_Env.pop_bv e  in
        match uu____1167 with
        | FStar_Pervasives_Native.None  -> b3
        | FStar_Pervasives_Native.Some (bv,e1) ->
            let b4 =
              b3 &&
                (FStar_TypeChecker_Env.closed e1 bv.FStar_Syntax_Syntax.sort)
               in
            aux b4 e1
         in
      let uu____1185 =
        (let uu____1188 = aux b2 env  in Prims.op_Negation uu____1188) &&
          (let uu____1190 = FStar_ST.op_Bang nwarn  in
           uu____1190 < (Prims.parse_int "5"))
         in
      (if uu____1185
       then
         ((let uu____1211 =
             let uu____1216 =
               let uu____1217 = goal_to_string g  in
               FStar_Util.format1
                 "The following goal is ill-formed. Keeping calm and carrying on...\n<%s>\n\n"
                 uu____1217
                in
             (FStar_Errors.Warning_IllFormedGoal, uu____1216)  in
           FStar_Errors.log_issue
             (g.FStar_Tactics_Types.goal_ty).FStar_Syntax_Syntax.pos
             uu____1211);
          (let uu____1218 =
             let uu____1219 = FStar_ST.op_Bang nwarn  in
             uu____1219 + (Prims.parse_int "1")  in
           FStar_ST.op_Colon_Equals nwarn uu____1218))
       else ())
    else ()
  
let (add_goals : FStar_Tactics_Types.goal Prims.list -> Prims.unit tac) =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___65_1277 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___65_1277.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___65_1277.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___65_1277.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (FStar_List.append gs p.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___65_1277.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___65_1277.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___65_1277.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___65_1277.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___65_1277.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___65_1277.FStar_Tactics_Types.guard_policy)
            }))
  
let (add_smt_goals : FStar_Tactics_Types.goal Prims.list -> Prims.unit tac) =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___66_1295 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___66_1295.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___66_1295.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___66_1295.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___66_1295.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (FStar_List.append gs p.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___66_1295.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___66_1295.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___66_1295.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___66_1295.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___66_1295.FStar_Tactics_Types.guard_policy)
            }))
  
let (push_goals : FStar_Tactics_Types.goal Prims.list -> Prims.unit tac) =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___67_1313 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___67_1313.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___67_1313.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___67_1313.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (FStar_List.append p.FStar_Tactics_Types.goals gs);
              FStar_Tactics_Types.smt_goals =
                (uu___67_1313.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___67_1313.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___67_1313.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___67_1313.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___67_1313.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___67_1313.FStar_Tactics_Types.guard_policy)
            }))
  
let (push_smt_goals : FStar_Tactics_Types.goal Prims.list -> Prims.unit tac)
  =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___68_1331 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___68_1331.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___68_1331.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___68_1331.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___68_1331.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (FStar_List.append p.FStar_Tactics_Types.smt_goals gs);
              FStar_Tactics_Types.depth =
                (uu___68_1331.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___68_1331.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___68_1331.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___68_1331.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___68_1331.FStar_Tactics_Types.guard_policy)
            }))
  
let (replace_cur : FStar_Tactics_Types.goal -> Prims.unit tac) =
  fun g  -> bind __dismiss (fun uu____1340  -> add_goals [g]) 
let (add_implicits : implicits -> Prims.unit tac) =
  fun i  ->
    bind get
      (fun p  ->
         set
           (let uu___69_1352 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___69_1352.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___69_1352.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (FStar_List.append i p.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___69_1352.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___69_1352.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___69_1352.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___69_1352.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___69_1352.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___69_1352.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___69_1352.FStar_Tactics_Types.guard_policy)
            }))
  
let (new_uvar :
  Prims.string ->
    env -> FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.term tac)
  =
  fun reason  ->
    fun env  ->
      fun typ  ->
        let uu____1378 =
          FStar_TypeChecker_Util.new_implicit_var reason
            typ.FStar_Syntax_Syntax.pos env typ
           in
        match uu____1378 with
        | (u,uu____1394,g_u) ->
            let uu____1408 =
              add_implicits g_u.FStar_TypeChecker_Env.implicits  in
            bind uu____1408 (fun uu____1412  -> ret u)
  
let (is_true : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____1416 = FStar_Syntax_Util.un_squash t  in
    match uu____1416 with
    | FStar_Pervasives_Native.Some t' ->
        let uu____1426 =
          let uu____1427 = FStar_Syntax_Subst.compress t'  in
          uu____1427.FStar_Syntax_Syntax.n  in
        (match uu____1426 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.true_lid
         | uu____1431 -> false)
    | uu____1432 -> false
  
let (is_false : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____1440 = FStar_Syntax_Util.un_squash t  in
    match uu____1440 with
    | FStar_Pervasives_Native.Some t' ->
        let uu____1450 =
          let uu____1451 = FStar_Syntax_Subst.compress t'  in
          uu____1451.FStar_Syntax_Syntax.n  in
        (match uu____1450 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.false_lid
         | uu____1455 -> false)
    | uu____1456 -> false
  
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
            let uu____1496 = env.FStar_TypeChecker_Env.universe_of env phi
               in
            FStar_Syntax_Util.mk_squash uu____1496 phi  in
          let uu____1497 = new_uvar reason env typ  in
          bind uu____1497
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
             let uu____1553 =
               (ps.FStar_Tactics_Types.main_context).FStar_TypeChecker_Env.type_of
                 e t
                in
             ret uu____1553
           with
           | FStar_Errors.Err (uu____1580,msg) ->
               let uu____1582 = tts e t  in
               let uu____1583 =
                 let uu____1584 = FStar_TypeChecker_Env.all_binders e  in
                 FStar_All.pipe_right uu____1584
                   (FStar_Syntax_Print.binders_to_string ", ")
                  in
               fail3 "Cannot type %s in context (%s). Error = (%s)"
                 uu____1582 uu____1583 msg
           | FStar_Errors.Error (uu____1591,msg,uu____1593) ->
               let uu____1594 = tts e t  in
               let uu____1595 =
                 let uu____1596 = FStar_TypeChecker_Env.all_binders e  in
                 FStar_All.pipe_right uu____1596
                   (FStar_Syntax_Print.binders_to_string ", ")
                  in
               fail3 "Cannot type %s in context (%s). Error = (%s)"
                 uu____1594 uu____1595 msg)
  
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
           (let uu___72_1630 = ps  in
            {
              FStar_Tactics_Types.main_context =
                (uu___72_1630.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___72_1630.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___72_1630.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___72_1630.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___72_1630.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___72_1630.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___72_1630.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___72_1630.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___72_1630.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy = pol
            }))
  
let with_policy : 'a . FStar_Tactics_Types.guard_policy -> 'a tac -> 'a tac =
  fun pol  ->
    fun t  ->
      bind get_guard_policy
        (fun old_pol  ->
           let uu____1652 = set_guard_policy pol  in
           bind uu____1652
             (fun uu____1656  ->
                bind t
                  (fun r  ->
                     let uu____1660 = set_guard_policy old_pol  in
                     bind uu____1660 (fun uu____1664  -> ret r))))
  
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
          let uu____1681 =
            let uu____1682 = FStar_TypeChecker_Rel.simplify_guard e g  in
            uu____1682.FStar_TypeChecker_Env.guard_f  in
          match uu____1681 with
          | FStar_TypeChecker_Common.Trivial  -> ret ()
          | FStar_TypeChecker_Common.NonTrivial f ->
              let uu____1686 = istrivial e f  in
              if uu____1686
              then ret ()
              else
                bind get
                  (fun ps  ->
                     match ps.FStar_Tactics_Types.guard_policy with
                     | FStar_Tactics_Types.Drop  -> ret ()
                     | FStar_Tactics_Types.Goal  ->
                         let uu____1694 = mk_irrelevant_goal reason e f opts
                            in
                         bind uu____1694
                           (fun goal  ->
                              let goal1 =
                                let uu___73_1701 = goal  in
                                {
                                  FStar_Tactics_Types.context =
                                    (uu___73_1701.FStar_Tactics_Types.context);
                                  FStar_Tactics_Types.witness =
                                    (uu___73_1701.FStar_Tactics_Types.witness);
                                  FStar_Tactics_Types.goal_ty =
                                    (uu___73_1701.FStar_Tactics_Types.goal_ty);
                                  FStar_Tactics_Types.opts =
                                    (uu___73_1701.FStar_Tactics_Types.opts);
                                  FStar_Tactics_Types.is_guard = true
                                }  in
                              push_goals [goal1])
                     | FStar_Tactics_Types.SMT  ->
                         let uu____1702 = mk_irrelevant_goal reason e f opts
                            in
                         bind uu____1702
                           (fun goal  ->
                              let goal1 =
                                let uu___74_1709 = goal  in
                                {
                                  FStar_Tactics_Types.context =
                                    (uu___74_1709.FStar_Tactics_Types.context);
                                  FStar_Tactics_Types.witness =
                                    (uu___74_1709.FStar_Tactics_Types.witness);
                                  FStar_Tactics_Types.goal_ty =
                                    (uu___74_1709.FStar_Tactics_Types.goal_ty);
                                  FStar_Tactics_Types.opts =
                                    (uu___74_1709.FStar_Tactics_Types.opts);
                                  FStar_Tactics_Types.is_guard = true
                                }  in
                              push_smt_goals [goal1])
                     | FStar_Tactics_Types.Force  ->
                         (try
                            let uu____1717 =
                              let uu____1718 =
                                let uu____1719 =
                                  FStar_TypeChecker_Rel.discharge_guard_no_smt
                                    e g
                                   in
                                FStar_All.pipe_left
                                  FStar_TypeChecker_Rel.is_trivial uu____1719
                                 in
                              Prims.op_Negation uu____1718  in
                            if uu____1717
                            then
                              mlog
                                (fun uu____1724  ->
                                   let uu____1725 =
                                     FStar_TypeChecker_Rel.guard_to_string e
                                       g
                                      in
                                   FStar_Util.print1 "guard = %s\n"
                                     uu____1725)
                                (fun uu____1727  ->
                                   fail1 "Forcing the guard failed %s)"
                                     reason)
                            else ret ()
                          with
                          | uu____1734 ->
                              mlog
                                (fun uu____1737  ->
                                   let uu____1738 =
                                     FStar_TypeChecker_Rel.guard_to_string e
                                       g
                                      in
                                   FStar_Util.print1 "guard = %s\n"
                                     uu____1738)
                                (fun uu____1740  ->
                                   fail1 "Forcing the guard failed (%s)"
                                     reason)))
  
let (tc : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.typ tac) =
  fun t  ->
    let uu____1748 =
      bind cur_goal
        (fun goal  ->
           let uu____1754 = __tc goal.FStar_Tactics_Types.context t  in
           bind uu____1754
             (fun uu____1774  ->
                match uu____1774 with
                | (t1,typ,guard) ->
                    let uu____1786 =
                      proc_guard "tc" goal.FStar_Tactics_Types.context guard
                        goal.FStar_Tactics_Types.opts
                       in
                    bind uu____1786 (fun uu____1790  -> ret typ)))
       in
    FStar_All.pipe_left (wrap_err "tc") uu____1748
  
let (add_irrelevant_goal :
  Prims.string ->
    env ->
      FStar_Syntax_Syntax.typ -> FStar_Options.optionstate -> Prims.unit tac)
  =
  fun reason  ->
    fun env  ->
      fun phi  ->
        fun opts  ->
          let uu____1811 = mk_irrelevant_goal reason env phi opts  in
          bind uu____1811 (fun goal  -> add_goals [goal])
  
let (trivial : Prims.unit tac) =
  bind cur_goal
    (fun goal  ->
       let uu____1823 =
         istrivial goal.FStar_Tactics_Types.context
           goal.FStar_Tactics_Types.goal_ty
          in
       if uu____1823
       then solve goal FStar_Syntax_Util.exp_unit
       else
         (let uu____1827 =
            tts goal.FStar_Tactics_Types.context
              goal.FStar_Tactics_Types.goal_ty
             in
          fail1 "Not a trivial goal: %s" uu____1827))
  
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
          let uu____1848 =
            let uu____1849 = FStar_TypeChecker_Rel.simplify_guard e g  in
            uu____1849.FStar_TypeChecker_Env.guard_f  in
          match uu____1848 with
          | FStar_TypeChecker_Common.Trivial  ->
              ret FStar_Pervasives_Native.None
          | FStar_TypeChecker_Common.NonTrivial f ->
              let uu____1857 = istrivial e f  in
              if uu____1857
              then ret FStar_Pervasives_Native.None
              else
                (let uu____1865 = mk_irrelevant_goal reason e f opts  in
                 bind uu____1865
                   (fun goal  ->
                      ret
                        (FStar_Pervasives_Native.Some
                           (let uu___77_1875 = goal  in
                            {
                              FStar_Tactics_Types.context =
                                (uu___77_1875.FStar_Tactics_Types.context);
                              FStar_Tactics_Types.witness =
                                (uu___77_1875.FStar_Tactics_Types.witness);
                              FStar_Tactics_Types.goal_ty =
                                (uu___77_1875.FStar_Tactics_Types.goal_ty);
                              FStar_Tactics_Types.opts =
                                (uu___77_1875.FStar_Tactics_Types.opts);
                              FStar_Tactics_Types.is_guard = true
                            }))))
  
let (smt : Prims.unit tac) =
  bind cur_goal
    (fun g  ->
       let uu____1883 = is_irrelevant g  in
       if uu____1883
       then bind __dismiss (fun uu____1887  -> add_smt_goals [g])
       else
         (let uu____1889 =
            tts g.FStar_Tactics_Types.context g.FStar_Tactics_Types.goal_ty
             in
          fail1 "goal is not irrelevant: cannot dispatch to smt (%s)"
            uu____1889))
  
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
             let uu____1930 =
               try
                 let uu____1964 =
                   let uu____1973 = FStar_BigInt.to_int_fs n1  in
                   FStar_List.splitAt uu____1973 p.FStar_Tactics_Types.goals
                    in
                 ret uu____1964
               with | uu____1995 -> fail "divide: not enough goals"  in
             bind uu____1930
               (fun uu____2022  ->
                  match uu____2022 with
                  | (lgs,rgs) ->
                      let lp =
                        let uu___78_2048 = p  in
                        {
                          FStar_Tactics_Types.main_context =
                            (uu___78_2048.FStar_Tactics_Types.main_context);
                          FStar_Tactics_Types.main_goal =
                            (uu___78_2048.FStar_Tactics_Types.main_goal);
                          FStar_Tactics_Types.all_implicits =
                            (uu___78_2048.FStar_Tactics_Types.all_implicits);
                          FStar_Tactics_Types.goals = lgs;
                          FStar_Tactics_Types.smt_goals = [];
                          FStar_Tactics_Types.depth =
                            (uu___78_2048.FStar_Tactics_Types.depth);
                          FStar_Tactics_Types.__dump =
                            (uu___78_2048.FStar_Tactics_Types.__dump);
                          FStar_Tactics_Types.psc =
                            (uu___78_2048.FStar_Tactics_Types.psc);
                          FStar_Tactics_Types.entry_range =
                            (uu___78_2048.FStar_Tactics_Types.entry_range);
                          FStar_Tactics_Types.guard_policy =
                            (uu___78_2048.FStar_Tactics_Types.guard_policy)
                        }  in
                      let rp =
                        let uu___79_2050 = p  in
                        {
                          FStar_Tactics_Types.main_context =
                            (uu___79_2050.FStar_Tactics_Types.main_context);
                          FStar_Tactics_Types.main_goal =
                            (uu___79_2050.FStar_Tactics_Types.main_goal);
                          FStar_Tactics_Types.all_implicits =
                            (uu___79_2050.FStar_Tactics_Types.all_implicits);
                          FStar_Tactics_Types.goals = rgs;
                          FStar_Tactics_Types.smt_goals = [];
                          FStar_Tactics_Types.depth =
                            (uu___79_2050.FStar_Tactics_Types.depth);
                          FStar_Tactics_Types.__dump =
                            (uu___79_2050.FStar_Tactics_Types.__dump);
                          FStar_Tactics_Types.psc =
                            (uu___79_2050.FStar_Tactics_Types.psc);
                          FStar_Tactics_Types.entry_range =
                            (uu___79_2050.FStar_Tactics_Types.entry_range);
                          FStar_Tactics_Types.guard_policy =
                            (uu___79_2050.FStar_Tactics_Types.guard_policy)
                        }  in
                      let uu____2051 = set lp  in
                      bind uu____2051
                        (fun uu____2059  ->
                           bind l
                             (fun a  ->
                                bind get
                                  (fun lp'  ->
                                     let uu____2073 = set rp  in
                                     bind uu____2073
                                       (fun uu____2081  ->
                                          bind r
                                            (fun b  ->
                                               bind get
                                                 (fun rp'  ->
                                                    let p' =
                                                      let uu___80_2097 = p
                                                         in
                                                      {
                                                        FStar_Tactics_Types.main_context
                                                          =
                                                          (uu___80_2097.FStar_Tactics_Types.main_context);
                                                        FStar_Tactics_Types.main_goal
                                                          =
                                                          (uu___80_2097.FStar_Tactics_Types.main_goal);
                                                        FStar_Tactics_Types.all_implicits
                                                          =
                                                          (uu___80_2097.FStar_Tactics_Types.all_implicits);
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
                                                          (uu___80_2097.FStar_Tactics_Types.depth);
                                                        FStar_Tactics_Types.__dump
                                                          =
                                                          (uu___80_2097.FStar_Tactics_Types.__dump);
                                                        FStar_Tactics_Types.psc
                                                          =
                                                          (uu___80_2097.FStar_Tactics_Types.psc);
                                                        FStar_Tactics_Types.entry_range
                                                          =
                                                          (uu___80_2097.FStar_Tactics_Types.entry_range);
                                                        FStar_Tactics_Types.guard_policy
                                                          =
                                                          (uu___80_2097.FStar_Tactics_Types.guard_policy)
                                                      }  in
                                                    let uu____2098 = set p'
                                                       in
                                                    bind uu____2098
                                                      (fun uu____2106  ->
                                                         ret (a, b))))))))))
  
let focus : 'a . 'a tac -> 'a tac =
  fun f  ->
    let uu____2124 = divide FStar_BigInt.one f idtac  in
    bind uu____2124
      (fun uu____2137  -> match uu____2137 with | (a,()) -> ret a)
  
let rec map : 'a . 'a tac -> 'a Prims.list tac =
  fun tau  ->
    bind get
      (fun p  ->
         match p.FStar_Tactics_Types.goals with
         | [] -> ret []
         | uu____2171::uu____2172 ->
             let uu____2175 =
               let uu____2184 = map tau  in
               divide FStar_BigInt.one tau uu____2184  in
             bind uu____2175
               (fun uu____2202  ->
                  match uu____2202 with | (h,t) -> ret (h :: t)))
  
let (seq : Prims.unit tac -> Prims.unit tac -> Prims.unit tac) =
  fun t1  ->
    fun t2  ->
      let uu____2239 =
        bind t1
          (fun uu____2244  ->
             let uu____2245 = map t2  in
             bind uu____2245 (fun uu____2253  -> ret ()))
         in
      focus uu____2239
  
let (intro : FStar_Syntax_Syntax.binder tac) =
  let uu____2260 =
    bind cur_goal
      (fun goal  ->
         let uu____2269 =
           FStar_Syntax_Util.arrow_one goal.FStar_Tactics_Types.goal_ty  in
         match uu____2269 with
         | FStar_Pervasives_Native.Some (b,c) ->
             let uu____2284 =
               let uu____2285 = FStar_Syntax_Util.is_total_comp c  in
               Prims.op_Negation uu____2285  in
             if uu____2284
             then fail "Codomain is effectful"
             else
               (let env' =
                  FStar_TypeChecker_Env.push_binders
                    goal.FStar_Tactics_Types.context [b]
                   in
                let typ' = comp_to_typ c  in
                let uu____2291 = new_uvar "intro" env' typ'  in
                bind uu____2291
                  (fun u  ->
                     let uu____2297 =
                       let uu____2300 =
                         FStar_Syntax_Util.abs [b] u
                           FStar_Pervasives_Native.None
                          in
                       trysolve goal uu____2300  in
                     bind uu____2297
                       (fun bb  ->
                          if bb
                          then
                            let uu____2306 =
                              let uu____2309 =
                                let uu___83_2310 = goal  in
                                let uu____2311 = bnorm env' u  in
                                let uu____2312 = bnorm env' typ'  in
                                {
                                  FStar_Tactics_Types.context = env';
                                  FStar_Tactics_Types.witness = uu____2311;
                                  FStar_Tactics_Types.goal_ty = uu____2312;
                                  FStar_Tactics_Types.opts =
                                    (uu___83_2310.FStar_Tactics_Types.opts);
                                  FStar_Tactics_Types.is_guard =
                                    (uu___83_2310.FStar_Tactics_Types.is_guard)
                                }  in
                              replace_cur uu____2309  in
                            bind uu____2306 (fun uu____2314  -> ret b)
                          else fail "unification failed")))
         | FStar_Pervasives_Native.None  ->
             let uu____2320 =
               tts goal.FStar_Tactics_Types.context
                 goal.FStar_Tactics_Types.goal_ty
                in
             fail1 "goal is not an arrow (%s)" uu____2320)
     in
  FStar_All.pipe_left (wrap_err "intro") uu____2260 
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
       (let uu____2351 =
          FStar_Syntax_Util.arrow_one goal.FStar_Tactics_Types.goal_ty  in
        match uu____2351 with
        | FStar_Pervasives_Native.Some (b,c) ->
            let uu____2370 =
              let uu____2371 = FStar_Syntax_Util.is_total_comp c  in
              Prims.op_Negation uu____2371  in
            if uu____2370
            then fail "Codomain is effectful"
            else
              (let bv =
                 FStar_Syntax_Syntax.gen_bv "__recf"
                   FStar_Pervasives_Native.None
                   goal.FStar_Tactics_Types.goal_ty
                  in
               let bs =
                 let uu____2387 = FStar_Syntax_Syntax.mk_binder bv  in
                 [uu____2387; b]  in
               let env' =
                 FStar_TypeChecker_Env.push_binders
                   goal.FStar_Tactics_Types.context bs
                  in
               let uu____2389 =
                 let uu____2392 = comp_to_typ c  in
                 new_uvar "intro_rec" env' uu____2392  in
               bind uu____2389
                 (fun u  ->
                    let lb =
                      let uu____2407 =
                        FStar_Syntax_Util.abs [b] u
                          FStar_Pervasives_Native.None
                         in
                      FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl bv) []
                        goal.FStar_Tactics_Types.goal_ty
                        FStar_Parser_Const.effect_Tot_lid uu____2407 []
                        FStar_Range.dummyRange
                       in
                    let body = FStar_Syntax_Syntax.bv_to_name bv  in
                    let uu____2413 =
                      FStar_Syntax_Subst.close_let_rec [lb] body  in
                    match uu____2413 with
                    | (lbs,body1) ->
                        let tm =
                          FStar_Syntax_Syntax.mk
                            (FStar_Syntax_Syntax.Tm_let ((true, lbs), body1))
                            FStar_Pervasives_Native.None
                            (goal.FStar_Tactics_Types.witness).FStar_Syntax_Syntax.pos
                           in
                        let uu____2443 = trysolve goal tm  in
                        bind uu____2443
                          (fun bb  ->
                             if bb
                             then
                               let uu____2459 =
                                 let uu____2462 =
                                   let uu___84_2463 = goal  in
                                   let uu____2464 = bnorm env' u  in
                                   let uu____2465 =
                                     let uu____2466 = comp_to_typ c  in
                                     bnorm env' uu____2466  in
                                   {
                                     FStar_Tactics_Types.context = env';
                                     FStar_Tactics_Types.witness = uu____2464;
                                     FStar_Tactics_Types.goal_ty = uu____2465;
                                     FStar_Tactics_Types.opts =
                                       (uu___84_2463.FStar_Tactics_Types.opts);
                                     FStar_Tactics_Types.is_guard =
                                       (uu___84_2463.FStar_Tactics_Types.is_guard)
                                   }  in
                                 replace_cur uu____2462  in
                               bind uu____2459
                                 (fun uu____2473  ->
                                    let uu____2474 =
                                      let uu____2479 =
                                        FStar_Syntax_Syntax.mk_binder bv  in
                                      (uu____2479, b)  in
                                    ret uu____2474)
                             else fail "intro_rec: unification failed")))
        | FStar_Pervasives_Native.None  ->
            let uu____2493 =
              tts goal.FStar_Tactics_Types.context
                goal.FStar_Tactics_Types.goal_ty
               in
            fail1 "intro_rec: goal is not an arrow (%s)" uu____2493))
  
let (norm : FStar_Syntax_Embeddings.norm_step Prims.list -> Prims.unit tac) =
  fun s  ->
    bind cur_goal
      (fun goal  ->
         mlog
           (fun uu____2513  ->
              let uu____2514 =
                FStar_Syntax_Print.term_to_string
                  goal.FStar_Tactics_Types.witness
                 in
              FStar_Util.print1 "norm: witness = %s\n" uu____2514)
           (fun uu____2519  ->
              let steps =
                let uu____2523 = FStar_TypeChecker_Normalize.tr_norm_steps s
                   in
                FStar_List.append
                  [FStar_TypeChecker_Normalize.Reify;
                  FStar_TypeChecker_Normalize.UnfoldTac] uu____2523
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
                (let uu___85_2530 = goal  in
                 {
                   FStar_Tactics_Types.context =
                     (uu___85_2530.FStar_Tactics_Types.context);
                   FStar_Tactics_Types.witness = w;
                   FStar_Tactics_Types.goal_ty = t;
                   FStar_Tactics_Types.opts =
                     (uu___85_2530.FStar_Tactics_Types.opts);
                   FStar_Tactics_Types.is_guard =
                     (uu___85_2530.FStar_Tactics_Types.is_guard)
                 })))
  
let (norm_term_env :
  env ->
    FStar_Syntax_Embeddings.norm_step Prims.list ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac)
  =
  fun e  ->
    fun s  ->
      fun t  ->
        let uu____2548 =
          mlog
            (fun uu____2553  ->
               let uu____2554 = FStar_Syntax_Print.term_to_string t  in
               FStar_Util.print1 "norm_term: tm = %s\n" uu____2554)
            (fun uu____2556  ->
               bind get
                 (fun ps  ->
                    let opts =
                      match ps.FStar_Tactics_Types.goals with
                      | g::uu____2562 -> g.FStar_Tactics_Types.opts
                      | uu____2565 -> FStar_Options.peek ()  in
                    mlog
                      (fun uu____2570  ->
                         let uu____2571 =
                           tts ps.FStar_Tactics_Types.main_context t  in
                         FStar_Util.print1 "norm_term_env: t = %s\n"
                           uu____2571)
                      (fun uu____2574  ->
                         let uu____2575 = __tc e t  in
                         bind uu____2575
                           (fun uu____2596  ->
                              match uu____2596 with
                              | (t1,uu____2606,uu____2607) ->
                                  let steps =
                                    let uu____2611 =
                                      FStar_TypeChecker_Normalize.tr_norm_steps
                                        s
                                       in
                                    FStar_List.append
                                      [FStar_TypeChecker_Normalize.Reify;
                                      FStar_TypeChecker_Normalize.UnfoldTac]
                                      uu____2611
                                     in
                                  let t2 =
                                    normalize steps
                                      ps.FStar_Tactics_Types.main_context t1
                                     in
                                  ret t2))))
           in
        FStar_All.pipe_left (wrap_err "norm_term") uu____2548
  
let (refine_intro : Prims.unit tac) =
  let uu____2623 =
    bind cur_goal
      (fun g  ->
         let uu____2630 =
           FStar_TypeChecker_Rel.base_and_refinement
             g.FStar_Tactics_Types.context g.FStar_Tactics_Types.goal_ty
            in
         match uu____2630 with
         | (uu____2643,FStar_Pervasives_Native.None ) ->
             fail "not a refinement"
         | (t,FStar_Pervasives_Native.Some (bv,phi)) ->
             let g1 =
               let uu___86_2668 = g  in
               {
                 FStar_Tactics_Types.context =
                   (uu___86_2668.FStar_Tactics_Types.context);
                 FStar_Tactics_Types.witness =
                   (uu___86_2668.FStar_Tactics_Types.witness);
                 FStar_Tactics_Types.goal_ty = t;
                 FStar_Tactics_Types.opts =
                   (uu___86_2668.FStar_Tactics_Types.opts);
                 FStar_Tactics_Types.is_guard =
                   (uu___86_2668.FStar_Tactics_Types.is_guard)
               }  in
             let uu____2669 =
               let uu____2674 =
                 let uu____2679 =
                   let uu____2680 = FStar_Syntax_Syntax.mk_binder bv  in
                   [uu____2680]  in
                 FStar_Syntax_Subst.open_term uu____2679 phi  in
               match uu____2674 with
               | (bvs,phi1) ->
                   let uu____2687 =
                     let uu____2688 = FStar_List.hd bvs  in
                     FStar_Pervasives_Native.fst uu____2688  in
                   (uu____2687, phi1)
                in
             (match uu____2669 with
              | (bv1,phi1) ->
                  let uu____2701 =
                    let uu____2704 =
                      FStar_Syntax_Subst.subst
                        [FStar_Syntax_Syntax.NT
                           (bv1, (g.FStar_Tactics_Types.witness))] phi1
                       in
                    mk_irrelevant_goal "refine_intro refinement"
                      g.FStar_Tactics_Types.context uu____2704
                      g.FStar_Tactics_Types.opts
                     in
                  bind uu____2701
                    (fun g2  ->
                       bind __dismiss (fun uu____2708  -> add_goals [g1; g2]))))
     in
  FStar_All.pipe_left (wrap_err "refine_intro") uu____2623 
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
           let uu____2729 = __tc env t  in
           bind uu____2729
             (fun uu____2749  ->
                match uu____2749 with
                | (t1,typ,guard) ->
                    let uu____2761 =
                      proc_guard "__exact typing"
                        goal.FStar_Tactics_Types.context guard
                        goal.FStar_Tactics_Types.opts
                       in
                    bind uu____2761
                      (fun uu____2765  ->
                         mlog
                           (fun uu____2769  ->
                              let uu____2770 =
                                tts goal.FStar_Tactics_Types.context typ  in
                              let uu____2771 =
                                tts goal.FStar_Tactics_Types.context
                                  goal.FStar_Tactics_Types.goal_ty
                                 in
                              FStar_Util.print2 "exact: unifying %s and %s\n"
                                uu____2770 uu____2771)
                           (fun uu____2774  ->
                              let uu____2775 =
                                do_unify goal.FStar_Tactics_Types.context typ
                                  goal.FStar_Tactics_Types.goal_ty
                                 in
                              bind uu____2775
                                (fun b  ->
                                   if b
                                   then solve goal t1
                                   else
                                     (let uu____2783 =
                                        tts goal.FStar_Tactics_Types.context
                                          t1
                                         in
                                      let uu____2784 =
                                        tts goal.FStar_Tactics_Types.context
                                          typ
                                         in
                                      let uu____2785 =
                                        tts goal.FStar_Tactics_Types.context
                                          goal.FStar_Tactics_Types.goal_ty
                                         in
                                      let uu____2786 =
                                        tts goal.FStar_Tactics_Types.context
                                          goal.FStar_Tactics_Types.witness
                                         in
                                      fail4
                                        "%s : %s does not exactly solve the goal %s (witness = %s)"
                                        uu____2783 uu____2784 uu____2785
                                        uu____2786))))))
  
let (t_exact : Prims.bool -> FStar_Syntax_Syntax.term -> Prims.unit tac) =
  fun set_expected_typ1  ->
    fun tm  ->
      let uu____2797 =
        mlog
          (fun uu____2802  ->
             let uu____2803 = FStar_Syntax_Print.term_to_string tm  in
             FStar_Util.print1 "t_exact: tm = %s\n" uu____2803)
          (fun uu____2806  ->
             let uu____2807 =
               let uu____2814 = __exact_now set_expected_typ1 tm  in
               trytac' uu____2814  in
             bind uu____2807
               (fun uu___56_2823  ->
                  match uu___56_2823 with
                  | FStar_Util.Inr r -> ret ()
                  | FStar_Util.Inl e ->
                      let uu____2832 =
                        let uu____2839 =
                          let uu____2842 =
                            norm [FStar_Syntax_Embeddings.Delta]  in
                          bind uu____2842
                            (fun uu____2846  ->
                               bind refine_intro
                                 (fun uu____2848  ->
                                    __exact_now set_expected_typ1 tm))
                           in
                        trytac' uu____2839  in
                      bind uu____2832
                        (fun uu___55_2855  ->
                           match uu___55_2855 with
                           | FStar_Util.Inr r -> ret ()
                           | FStar_Util.Inl uu____2863 -> fail e)))
         in
      FStar_All.pipe_left (wrap_err "exact") uu____2797
  
let (uvar_free_in_goal :
  FStar_Syntax_Syntax.uvar -> FStar_Tactics_Types.goal -> Prims.bool) =
  fun u  ->
    fun g  ->
      if g.FStar_Tactics_Types.is_guard
      then false
      else
        (let free_uvars =
           let uu____2878 =
             let uu____2885 =
               FStar_Syntax_Free.uvars g.FStar_Tactics_Types.goal_ty  in
             FStar_Util.set_elements uu____2885  in
           FStar_List.map FStar_Pervasives_Native.fst uu____2878  in
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
          let uu____2945 = f x  in
          bind uu____2945
            (fun y  ->
               let uu____2953 = mapM f xs  in
               bind uu____2953 (fun ys  -> ret (y :: ys)))
  
exception NoUnif 
let (uu___is_NoUnif : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with | NoUnif  -> true | uu____2971 -> false
  
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
               (fun uu____2989  ->
                  let uu____2990 = FStar_Syntax_Print.term_to_string tm  in
                  FStar_Util.print1 ">>> Calling __exact(%s)\n" uu____2990)
               (fun uu____2993  ->
                  let uu____2994 =
                    let uu____2999 =
                      let uu____3002 = t_exact false tm  in
                      with_policy FStar_Tactics_Types.Force uu____3002  in
                    trytac_exn uu____2999  in
                  bind uu____2994
                    (fun uu___57_3009  ->
                       match uu___57_3009 with
                       | FStar_Pervasives_Native.Some r -> ret ()
                       | FStar_Pervasives_Native.None  ->
                           mlog
                             (fun uu____3017  ->
                                let uu____3018 =
                                  FStar_Syntax_Print.term_to_string typ  in
                                FStar_Util.print1 ">>> typ = %s\n" uu____3018)
                             (fun uu____3021  ->
                                let uu____3022 =
                                  FStar_Syntax_Util.arrow_one typ  in
                                match uu____3022 with
                                | FStar_Pervasives_Native.None  ->
                                    FStar_Exn.raise NoUnif
                                | FStar_Pervasives_Native.Some ((bv,aq),c) ->
                                    mlog
                                      (fun uu____3054  ->
                                         let uu____3055 =
                                           FStar_Syntax_Print.binder_to_string
                                             (bv, aq)
                                            in
                                         FStar_Util.print1
                                           "__apply: pushing binder %s\n"
                                           uu____3055)
                                      (fun uu____3058  ->
                                         let uu____3059 =
                                           let uu____3060 =
                                             FStar_Syntax_Util.is_total_comp
                                               c
                                              in
                                           Prims.op_Negation uu____3060  in
                                         if uu____3059
                                         then
                                           fail "apply: not total codomain"
                                         else
                                           (let uu____3064 =
                                              new_uvar "apply"
                                                goal.FStar_Tactics_Types.context
                                                bv.FStar_Syntax_Syntax.sort
                                               in
                                            bind uu____3064
                                              (fun u  ->
                                                 let tm' =
                                                   FStar_Syntax_Syntax.mk_Tm_app
                                                     tm [(u, aq)]
                                                     FStar_Pervasives_Native.None
                                                     tm.FStar_Syntax_Syntax.pos
                                                    in
                                                 let typ' =
                                                   let uu____3084 =
                                                     comp_to_typ c  in
                                                   FStar_All.pipe_left
                                                     (FStar_Syntax_Subst.subst
                                                        [FStar_Syntax_Syntax.NT
                                                           (bv, u)])
                                                     uu____3084
                                                    in
                                                 let uu____3085 =
                                                   __apply uopt tm' typ'  in
                                                 bind uu____3085
                                                   (fun uu____3093  ->
                                                      let u1 =
                                                        bnorm
                                                          goal.FStar_Tactics_Types.context
                                                          u
                                                         in
                                                      let uu____3095 =
                                                        let uu____3096 =
                                                          let uu____3099 =
                                                            let uu____3100 =
                                                              FStar_Syntax_Util.head_and_args
                                                                u1
                                                               in
                                                            FStar_Pervasives_Native.fst
                                                              uu____3100
                                                             in
                                                          FStar_Syntax_Subst.compress
                                                            uu____3099
                                                           in
                                                        uu____3096.FStar_Syntax_Syntax.n
                                                         in
                                                      match uu____3095 with
                                                      | FStar_Syntax_Syntax.Tm_uvar
                                                          (uvar,uu____3128)
                                                          ->
                                                          bind get
                                                            (fun ps  ->
                                                               let uu____3156
                                                                 =
                                                                 uopt &&
                                                                   (uvar_free
                                                                    uvar ps)
                                                                  in
                                                               if uu____3156
                                                               then ret ()
                                                               else
                                                                 (let uu____3160
                                                                    =
                                                                    let uu____3163
                                                                    =
                                                                    let uu___87_3164
                                                                    = goal
                                                                     in
                                                                    let uu____3165
                                                                    =
                                                                    bnorm
                                                                    goal.FStar_Tactics_Types.context
                                                                    u1  in
                                                                    let uu____3166
                                                                    =
                                                                    bnorm
                                                                    goal.FStar_Tactics_Types.context
                                                                    bv.FStar_Syntax_Syntax.sort
                                                                     in
                                                                    {
                                                                    FStar_Tactics_Types.context
                                                                    =
                                                                    (uu___87_3164.FStar_Tactics_Types.context);
                                                                    FStar_Tactics_Types.witness
                                                                    =
                                                                    uu____3165;
                                                                    FStar_Tactics_Types.goal_ty
                                                                    =
                                                                    uu____3166;
                                                                    FStar_Tactics_Types.opts
                                                                    =
                                                                    (uu___87_3164.FStar_Tactics_Types.opts);
                                                                    FStar_Tactics_Types.is_guard
                                                                    = false
                                                                    }  in
                                                                    [uu____3163]
                                                                     in
                                                                  add_goals
                                                                    uu____3160))
                                                      | t -> ret ()))))))))
  
let try_unif : 'a . 'a tac -> 'a tac -> 'a tac =
  fun t  ->
    fun t'  -> mk_tac (fun ps  -> try run t ps with | NoUnif  -> run t' ps)
  
let (apply : Prims.bool -> FStar_Syntax_Syntax.term -> Prims.unit tac) =
  fun uopt  ->
    fun tm  ->
      let uu____3212 =
        mlog
          (fun uu____3217  ->
             let uu____3218 = FStar_Syntax_Print.term_to_string tm  in
             FStar_Util.print1 "apply: tm = %s\n" uu____3218)
          (fun uu____3220  ->
             bind cur_goal
               (fun goal  ->
                  let uu____3224 = __tc goal.FStar_Tactics_Types.context tm
                     in
                  bind uu____3224
                    (fun uu____3246  ->
                       match uu____3246 with
                       | (tm1,typ,guard) ->
                           let typ1 =
                             bnorm goal.FStar_Tactics_Types.context typ  in
                           let uu____3259 =
                             let uu____3262 =
                               let uu____3265 = __apply uopt tm1 typ1  in
                               bind uu____3265
                                 (fun uu____3269  ->
                                    proc_guard "apply guard"
                                      goal.FStar_Tactics_Types.context guard
                                      goal.FStar_Tactics_Types.opts)
                                in
                             focus uu____3262  in
                           let uu____3270 =
                             let uu____3273 =
                               tts goal.FStar_Tactics_Types.context tm1  in
                             let uu____3274 =
                               tts goal.FStar_Tactics_Types.context typ1  in
                             let uu____3275 =
                               tts goal.FStar_Tactics_Types.context
                                 goal.FStar_Tactics_Types.goal_ty
                                in
                             fail3
                               "Cannot instantiate %s (of type %s) to match goal (%s)"
                               uu____3273 uu____3274 uu____3275
                              in
                           try_unif uu____3259 uu____3270)))
         in
      FStar_All.pipe_left (wrap_err "apply") uu____3212
  
let (lemma_or_sq :
  FStar_Syntax_Syntax.comp ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun c  ->
    let ct = FStar_Syntax_Util.comp_to_comp_typ_nouniv c  in
    if
      FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
        FStar_Parser_Const.effect_Lemma_lid
    then
      let uu____3302 =
        match ct.FStar_Syntax_Syntax.effect_args with
        | pre::post::uu____3321 ->
            ((FStar_Pervasives_Native.fst pre),
              (FStar_Pervasives_Native.fst post))
        | uu____3362 -> failwith "apply_lemma: impossible: not a lemma"  in
      match uu____3302 with
      | (pre,post) ->
          let post1 =
            let uu____3398 =
              let uu____3407 =
                FStar_Syntax_Syntax.as_arg FStar_Syntax_Util.exp_unit  in
              [uu____3407]  in
            FStar_Syntax_Util.mk_app post uu____3398  in
          FStar_Pervasives_Native.Some (pre, post1)
    else
      if FStar_Syntax_Util.is_pure_effect ct.FStar_Syntax_Syntax.effect_name
      then
        (let uu____3427 =
           FStar_Syntax_Util.un_squash ct.FStar_Syntax_Syntax.result_typ  in
         FStar_Util.map_opt uu____3427
           (fun post  -> (FStar_Syntax_Util.t_true, post)))
      else FStar_Pervasives_Native.None
  
let (apply_lemma : FStar_Syntax_Syntax.term -> Prims.unit tac) =
  fun tm  ->
    let uu____3458 =
      let uu____3461 =
        mlog
          (fun uu____3466  ->
             let uu____3467 = FStar_Syntax_Print.term_to_string tm  in
             FStar_Util.print1 "apply_lemma: tm = %s\n" uu____3467)
          (fun uu____3470  ->
             let is_unit_t t =
               let uu____3475 =
                 let uu____3476 = FStar_Syntax_Subst.compress t  in
                 uu____3476.FStar_Syntax_Syntax.n  in
               match uu____3475 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.unit_lid
                   -> true
               | uu____3480 -> false  in
             bind cur_goal
               (fun goal  ->
                  let uu____3484 = __tc goal.FStar_Tactics_Types.context tm
                     in
                  bind uu____3484
                    (fun uu____3507  ->
                       match uu____3507 with
                       | (tm1,t,guard) ->
                           let uu____3519 =
                             FStar_Syntax_Util.arrow_formals_comp t  in
                           (match uu____3519 with
                            | (bs,comp) ->
                                let uu____3546 = lemma_or_sq comp  in
                                (match uu____3546 with
                                 | FStar_Pervasives_Native.None  ->
                                     fail "not a lemma or squashed function"
                                 | FStar_Pervasives_Native.Some (pre,post) ->
                                     let uu____3565 =
                                       FStar_List.fold_left
                                         (fun uu____3611  ->
                                            fun uu____3612  ->
                                              match (uu____3611, uu____3612)
                                              with
                                              | ((uvs,guard1,subst1),(b,aq))
                                                  ->
                                                  let b_t =
                                                    FStar_Syntax_Subst.subst
                                                      subst1
                                                      b.FStar_Syntax_Syntax.sort
                                                     in
                                                  let uu____3715 =
                                                    is_unit_t b_t  in
                                                  if uu____3715
                                                  then
                                                    (((FStar_Syntax_Util.exp_unit,
                                                        aq) :: uvs), guard1,
                                                      ((FStar_Syntax_Syntax.NT
                                                          (b,
                                                            FStar_Syntax_Util.exp_unit))
                                                      :: subst1))
                                                  else
                                                    (let uu____3753 =
                                                       FStar_TypeChecker_Util.new_implicit_var
                                                         "apply_lemma"
                                                         (goal.FStar_Tactics_Types.goal_ty).FStar_Syntax_Syntax.pos
                                                         goal.FStar_Tactics_Types.context
                                                         b_t
                                                        in
                                                     match uu____3753 with
                                                     | (u,uu____3783,g_u) ->
                                                         let uu____3797 =
                                                           FStar_TypeChecker_Rel.conj_guard
                                                             guard1 g_u
                                                            in
                                                         (((u, aq) :: uvs),
                                                           uu____3797,
                                                           ((FStar_Syntax_Syntax.NT
                                                               (b, u)) ::
                                                           subst1))))
                                         ([], guard, []) bs
                                        in
                                     (match uu____3565 with
                                      | (uvs,implicits,subst1) ->
                                          let uvs1 = FStar_List.rev uvs  in
                                          let pre1 =
                                            FStar_Syntax_Subst.subst subst1
                                              pre
                                             in
                                          let post1 =
                                            FStar_Syntax_Subst.subst subst1
                                              post
                                             in
                                          let uu____3868 =
                                            let uu____3871 =
                                              FStar_Syntax_Util.mk_squash
                                                FStar_Syntax_Syntax.U_zero
                                                post1
                                               in
                                            do_unify
                                              goal.FStar_Tactics_Types.context
                                              uu____3871
                                              goal.FStar_Tactics_Types.goal_ty
                                             in
                                          bind uu____3868
                                            (fun b  ->
                                               if Prims.op_Negation b
                                               then
                                                 let uu____3879 =
                                                   tts
                                                     goal.FStar_Tactics_Types.context
                                                     tm1
                                                    in
                                                 let uu____3880 =
                                                   let uu____3881 =
                                                     FStar_Syntax_Util.mk_squash
                                                       FStar_Syntax_Syntax.U_zero
                                                       post1
                                                      in
                                                   tts
                                                     goal.FStar_Tactics_Types.context
                                                     uu____3881
                                                    in
                                                 let uu____3882 =
                                                   tts
                                                     goal.FStar_Tactics_Types.context
                                                     goal.FStar_Tactics_Types.goal_ty
                                                    in
                                                 fail3
                                                   "Cannot instantiate lemma %s (with postcondition: %s) to match goal (%s)"
                                                   uu____3879 uu____3880
                                                   uu____3882
                                               else
                                                 (let uu____3884 =
                                                    add_implicits
                                                      implicits.FStar_TypeChecker_Env.implicits
                                                     in
                                                  bind uu____3884
                                                    (fun uu____3889  ->
                                                       let uu____3890 =
                                                         solve goal
                                                           FStar_Syntax_Util.exp_unit
                                                          in
                                                       bind uu____3890
                                                         (fun uu____3898  ->
                                                            let is_free_uvar
                                                              uv t1 =
                                                              let free_uvars
                                                                =
                                                                let uu____3909
                                                                  =
                                                                  let uu____3916
                                                                    =
                                                                    FStar_Syntax_Free.uvars
                                                                    t1  in
                                                                  FStar_Util.set_elements
                                                                    uu____3916
                                                                   in
                                                                FStar_List.map
                                                                  FStar_Pervasives_Native.fst
                                                                  uu____3909
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
                                                              let uu____3957
                                                                =
                                                                FStar_Syntax_Util.head_and_args
                                                                  t1
                                                                 in
                                                              match uu____3957
                                                              with
                                                              | (hd1,uu____3973)
                                                                  ->
                                                                  (match 
                                                                    hd1.FStar_Syntax_Syntax.n
                                                                   with
                                                                   | 
                                                                   FStar_Syntax_Syntax.Tm_uvar
                                                                    (uv,uu____3995)
                                                                    ->
                                                                    appears
                                                                    uv goals
                                                                   | 
                                                                   uu____4020
                                                                    -> false)
                                                               in
                                                            let uu____4021 =
                                                              FStar_All.pipe_right
                                                                implicits.FStar_TypeChecker_Env.implicits
                                                                (mapM
                                                                   (fun
                                                                    uu____4093
                                                                     ->
                                                                    match uu____4093
                                                                    with
                                                                    | 
                                                                    (_msg,env,_uvar,term,typ,uu____4121)
                                                                    ->
                                                                    let uu____4122
                                                                    =
                                                                    FStar_Syntax_Util.head_and_args
                                                                    term  in
                                                                    (match uu____4122
                                                                    with
                                                                    | 
                                                                    (hd1,uu____4148)
                                                                    ->
                                                                    let uu____4169
                                                                    =
                                                                    let uu____4170
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    hd1  in
                                                                    uu____4170.FStar_Syntax_Syntax.n
                                                                     in
                                                                    (match uu____4169
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Tm_uvar
                                                                    uu____4183
                                                                    ->
                                                                    let uu____4200
                                                                    =
                                                                    let uu____4209
                                                                    =
                                                                    let uu____4212
                                                                    =
                                                                    let uu___90_4213
                                                                    = goal
                                                                     in
                                                                    let uu____4214
                                                                    =
                                                                    bnorm
                                                                    goal.FStar_Tactics_Types.context
                                                                    term  in
                                                                    let uu____4215
                                                                    =
                                                                    bnorm
                                                                    goal.FStar_Tactics_Types.context
                                                                    typ  in
                                                                    {
                                                                    FStar_Tactics_Types.context
                                                                    =
                                                                    (uu___90_4213.FStar_Tactics_Types.context);
                                                                    FStar_Tactics_Types.witness
                                                                    =
                                                                    uu____4214;
                                                                    FStar_Tactics_Types.goal_ty
                                                                    =
                                                                    uu____4215;
                                                                    FStar_Tactics_Types.opts
                                                                    =
                                                                    (uu___90_4213.FStar_Tactics_Types.opts);
                                                                    FStar_Tactics_Types.is_guard
                                                                    =
                                                                    (uu___90_4213.FStar_Tactics_Types.is_guard)
                                                                    }  in
                                                                    [uu____4212]
                                                                     in
                                                                    (uu____4209,
                                                                    [])  in
                                                                    ret
                                                                    uu____4200
                                                                    | 
                                                                    uu____4228
                                                                    ->
                                                                    let g_typ
                                                                    =
                                                                    let uu____4230
                                                                    =
                                                                    FStar_Options.__temp_fast_implicits
                                                                    ()  in
                                                                    if
                                                                    uu____4230
                                                                    then
                                                                    FStar_TypeChecker_TcTerm.check_type_of_well_typed_term
                                                                    false env
                                                                    term typ
                                                                    else
                                                                    (let term1
                                                                    =
                                                                    bnorm env
                                                                    term  in
                                                                    let uu____4233
                                                                    =
                                                                    let uu____4240
                                                                    =
                                                                    FStar_TypeChecker_Env.set_expected_typ
                                                                    env typ
                                                                     in
                                                                    env.FStar_TypeChecker_Env.type_of
                                                                    uu____4240
                                                                    term1  in
                                                                    match uu____4233
                                                                    with
                                                                    | 
                                                                    (uu____4241,uu____4242,g_typ)
                                                                    -> g_typ)
                                                                     in
                                                                    let uu____4244
                                                                    =
                                                                    goal_from_guard
                                                                    "apply_lemma solved arg"
                                                                    goal.FStar_Tactics_Types.context
                                                                    g_typ
                                                                    goal.FStar_Tactics_Types.opts
                                                                     in
                                                                    bind
                                                                    uu____4244
                                                                    (fun
                                                                    uu___58_4260
                                                                     ->
                                                                    match uu___58_4260
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
                                                            bind uu____4021
                                                              (fun goals_  ->
                                                                 let sub_goals
                                                                   =
                                                                   let uu____4328
                                                                    =
                                                                    FStar_List.map
                                                                    FStar_Pervasives_Native.fst
                                                                    goals_
                                                                     in
                                                                   FStar_List.flatten
                                                                    uu____4328
                                                                    in
                                                                 let smt_goals
                                                                   =
                                                                   let uu____4350
                                                                    =
                                                                    FStar_List.map
                                                                    FStar_Pervasives_Native.snd
                                                                    goals_
                                                                     in
                                                                   FStar_List.flatten
                                                                    uu____4350
                                                                    in
                                                                 let rec filter'
                                                                   a f xs =
                                                                   match xs
                                                                   with
                                                                   | 
                                                                   [] -> []
                                                                   | 
                                                                   x::xs1 ->
                                                                    let uu____4405
                                                                    = f x xs1
                                                                     in
                                                                    if
                                                                    uu____4405
                                                                    then
                                                                    let uu____4408
                                                                    =
                                                                    filter'
                                                                    () f xs1
                                                                     in x ::
                                                                    uu____4408
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
                                                                    let uu____4422
                                                                    =
                                                                    checkone
                                                                    g.FStar_Tactics_Types.witness
                                                                    goals  in
                                                                    Prims.op_Negation
                                                                    uu____4422))
                                                                    a438 a439)
                                                                    (Obj.magic
                                                                    sub_goals))
                                                                    in
                                                                 let uu____4423
                                                                   =
                                                                   proc_guard
                                                                    "apply_lemma guard"
                                                                    goal.FStar_Tactics_Types.context
                                                                    guard
                                                                    goal.FStar_Tactics_Types.opts
                                                                    in
                                                                 bind
                                                                   uu____4423
                                                                   (fun
                                                                    uu____4428
                                                                     ->
                                                                    let uu____4429
                                                                    =
                                                                    let uu____4432
                                                                    =
                                                                    let uu____4433
                                                                    =
                                                                    let uu____4434
                                                                    =
                                                                    FStar_Syntax_Util.mk_squash
                                                                    FStar_Syntax_Syntax.U_zero
                                                                    pre1  in
                                                                    istrivial
                                                                    goal.FStar_Tactics_Types.context
                                                                    uu____4434
                                                                     in
                                                                    Prims.op_Negation
                                                                    uu____4433
                                                                     in
                                                                    if
                                                                    uu____4432
                                                                    then
                                                                    add_irrelevant_goal
                                                                    "apply_lemma precondition"
                                                                    goal.FStar_Tactics_Types.context
                                                                    pre1
                                                                    goal.FStar_Tactics_Types.opts
                                                                    else
                                                                    ret ()
                                                                     in
                                                                    bind
                                                                    uu____4429
                                                                    (fun
                                                                    uu____4440
                                                                     ->
                                                                    let uu____4441
                                                                    =
                                                                    add_smt_goals
                                                                    smt_goals
                                                                     in
                                                                    bind
                                                                    uu____4441
                                                                    (fun
                                                                    uu____4445
                                                                     ->
                                                                    add_goals
                                                                    sub_goals1))))))))))))))
         in
      focus uu____3461  in
    FStar_All.pipe_left (wrap_err "apply_lemma") uu____3458
  
let (destruct_eq' :
  FStar_Syntax_Syntax.typ ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun typ  ->
    let uu____4465 = FStar_Syntax_Util.destruct_typ_as_formula typ  in
    match uu____4465 with
    | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn
        (l,uu____4475::(e1,uu____4477)::(e2,uu____4479)::[])) when
        FStar_Ident.lid_equals l FStar_Parser_Const.eq2_lid ->
        FStar_Pervasives_Native.Some (e1, e2)
    | uu____4538 -> FStar_Pervasives_Native.None
  
let (destruct_eq :
  FStar_Syntax_Syntax.typ ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun typ  ->
    let uu____4560 = destruct_eq' typ  in
    match uu____4560 with
    | FStar_Pervasives_Native.Some t -> FStar_Pervasives_Native.Some t
    | FStar_Pervasives_Native.None  ->
        let uu____4590 = FStar_Syntax_Util.un_squash typ  in
        (match uu____4590 with
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
        let uu____4646 = FStar_TypeChecker_Env.pop_bv e1  in
        match uu____4646 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (bv',e') ->
            if FStar_Syntax_Syntax.bv_eq bvar bv'
            then FStar_Pervasives_Native.Some (e', [])
            else
              (let uu____4694 = aux e'  in
               FStar_Util.map_opt uu____4694
                 (fun uu____4718  ->
                    match uu____4718 with | (e'',bvs) -> (e'', (bv' :: bvs))))
         in
      let uu____4739 = aux e  in
      FStar_Util.map_opt uu____4739
        (fun uu____4763  ->
           match uu____4763 with | (e',bvs) -> (e', (FStar_List.rev bvs)))
  
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
          let uu____4818 = split_env b1 g.FStar_Tactics_Types.context  in
          FStar_Util.map_opt uu____4818
            (fun uu____4842  ->
               match uu____4842 with
               | (e0,bvs) ->
                   let s1 bv =
                     let uu___91_4859 = bv  in
                     let uu____4860 =
                       FStar_Syntax_Subst.subst s bv.FStar_Syntax_Syntax.sort
                        in
                     {
                       FStar_Syntax_Syntax.ppname =
                         (uu___91_4859.FStar_Syntax_Syntax.ppname);
                       FStar_Syntax_Syntax.index =
                         (uu___91_4859.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort = uu____4860
                     }  in
                   let bvs1 = FStar_List.map s1 bvs  in
                   let c = push_bvs e0 (b2 :: bvs1)  in
                   let w =
                     FStar_Syntax_Subst.subst s g.FStar_Tactics_Types.witness
                      in
                   let t =
                     FStar_Syntax_Subst.subst s g.FStar_Tactics_Types.goal_ty
                      in
                   let uu___92_4869 = g  in
                   {
                     FStar_Tactics_Types.context = c;
                     FStar_Tactics_Types.witness = w;
                     FStar_Tactics_Types.goal_ty = t;
                     FStar_Tactics_Types.opts =
                       (uu___92_4869.FStar_Tactics_Types.opts);
                     FStar_Tactics_Types.is_guard =
                       (uu___92_4869.FStar_Tactics_Types.is_guard)
                   })
  
let (rewrite : FStar_Syntax_Syntax.binder -> Prims.unit tac) =
  fun h  ->
    bind cur_goal
      (fun goal  ->
         let uu____4882 = h  in
         match uu____4882 with
         | (bv,uu____4886) ->
             mlog
               (fun uu____4890  ->
                  let uu____4891 = FStar_Syntax_Print.bv_to_string bv  in
                  let uu____4892 =
                    tts goal.FStar_Tactics_Types.context
                      bv.FStar_Syntax_Syntax.sort
                     in
                  FStar_Util.print2 "+++Rewrite %s : %s\n" uu____4891
                    uu____4892)
               (fun uu____4895  ->
                  let uu____4896 =
                    split_env bv goal.FStar_Tactics_Types.context  in
                  match uu____4896 with
                  | FStar_Pervasives_Native.None  ->
                      fail "rewrite: binder not found in environment"
                  | FStar_Pervasives_Native.Some (e0,bvs) ->
                      let uu____4925 =
                        destruct_eq bv.FStar_Syntax_Syntax.sort  in
                      (match uu____4925 with
                       | FStar_Pervasives_Native.Some (x,e) ->
                           let uu____4940 =
                             let uu____4941 = FStar_Syntax_Subst.compress x
                                in
                             uu____4941.FStar_Syntax_Syntax.n  in
                           (match uu____4940 with
                            | FStar_Syntax_Syntax.Tm_name x1 ->
                                let s = [FStar_Syntax_Syntax.NT (x1, e)]  in
                                let s1 bv1 =
                                  let uu___93_4954 = bv1  in
                                  let uu____4955 =
                                    FStar_Syntax_Subst.subst s
                                      bv1.FStar_Syntax_Syntax.sort
                                     in
                                  {
                                    FStar_Syntax_Syntax.ppname =
                                      (uu___93_4954.FStar_Syntax_Syntax.ppname);
                                    FStar_Syntax_Syntax.index =
                                      (uu___93_4954.FStar_Syntax_Syntax.index);
                                    FStar_Syntax_Syntax.sort = uu____4955
                                  }  in
                                let bvs1 = FStar_List.map s1 bvs  in
                                let uu____4961 =
                                  let uu___94_4962 = goal  in
                                  let uu____4963 = push_bvs e0 (bv :: bvs1)
                                     in
                                  let uu____4964 =
                                    FStar_Syntax_Subst.subst s
                                      goal.FStar_Tactics_Types.witness
                                     in
                                  let uu____4965 =
                                    FStar_Syntax_Subst.subst s
                                      goal.FStar_Tactics_Types.goal_ty
                                     in
                                  {
                                    FStar_Tactics_Types.context = uu____4963;
                                    FStar_Tactics_Types.witness = uu____4964;
                                    FStar_Tactics_Types.goal_ty = uu____4965;
                                    FStar_Tactics_Types.opts =
                                      (uu___94_4962.FStar_Tactics_Types.opts);
                                    FStar_Tactics_Types.is_guard =
                                      (uu___94_4962.FStar_Tactics_Types.is_guard)
                                  }  in
                                replace_cur uu____4961
                            | uu____4966 ->
                                fail
                                  "rewrite: Not an equality hypothesis with a variable on the LHS")
                       | uu____4967 ->
                           fail "rewrite: Not an equality hypothesis")))
  
let (rename_to :
  FStar_Syntax_Syntax.binder -> Prims.string -> Prims.unit tac) =
  fun b  ->
    fun s  ->
      bind cur_goal
        (fun goal  ->
           let uu____4992 = b  in
           match uu____4992 with
           | (bv,uu____4996) ->
               let bv' =
                 FStar_Syntax_Syntax.freshen_bv
                   (let uu___95_5000 = bv  in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (FStar_Ident.mk_ident
                           (s,
                             ((bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange)));
                      FStar_Syntax_Syntax.index =
                        (uu___95_5000.FStar_Syntax_Syntax.index);
                      FStar_Syntax_Syntax.sort =
                        (uu___95_5000.FStar_Syntax_Syntax.sort)
                    })
                  in
               let s1 =
                 let uu____5004 =
                   let uu____5005 =
                     let uu____5012 = FStar_Syntax_Syntax.bv_to_name bv'  in
                     (bv, uu____5012)  in
                   FStar_Syntax_Syntax.NT uu____5005  in
                 [uu____5004]  in
               let uu____5013 = subst_goal bv bv' s1 goal  in
               (match uu____5013 with
                | FStar_Pervasives_Native.None  ->
                    fail "rename_to: binder not found in environment"
                | FStar_Pervasives_Native.Some goal1 -> replace_cur goal1))
  
let (binder_retype : FStar_Syntax_Syntax.binder -> Prims.unit tac) =
  fun b  ->
    bind cur_goal
      (fun goal  ->
         let uu____5032 = b  in
         match uu____5032 with
         | (bv,uu____5036) ->
             let uu____5037 = split_env bv goal.FStar_Tactics_Types.context
                in
             (match uu____5037 with
              | FStar_Pervasives_Native.None  ->
                  fail "binder_retype: binder is not present in environment"
              | FStar_Pervasives_Native.Some (e0,bvs) ->
                  let uu____5066 = FStar_Syntax_Util.type_u ()  in
                  (match uu____5066 with
                   | (ty,u) ->
                       let uu____5075 = new_uvar "binder_retype" e0 ty  in
                       bind uu____5075
                         (fun t'  ->
                            let bv'' =
                              let uu___96_5085 = bv  in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___96_5085.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___96_5085.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = t'
                              }  in
                            let s =
                              let uu____5089 =
                                let uu____5090 =
                                  let uu____5097 =
                                    FStar_Syntax_Syntax.bv_to_name bv''  in
                                  (bv, uu____5097)  in
                                FStar_Syntax_Syntax.NT uu____5090  in
                              [uu____5089]  in
                            let bvs1 =
                              FStar_List.map
                                (fun b1  ->
                                   let uu___97_5105 = b1  in
                                   let uu____5106 =
                                     FStar_Syntax_Subst.subst s
                                       b1.FStar_Syntax_Syntax.sort
                                      in
                                   {
                                     FStar_Syntax_Syntax.ppname =
                                       (uu___97_5105.FStar_Syntax_Syntax.ppname);
                                     FStar_Syntax_Syntax.index =
                                       (uu___97_5105.FStar_Syntax_Syntax.index);
                                     FStar_Syntax_Syntax.sort = uu____5106
                                   }) bvs
                               in
                            let env' = push_bvs e0 (bv'' :: bvs1)  in
                            bind __dismiss
                              (fun uu____5112  ->
                                 let uu____5113 =
                                   let uu____5116 =
                                     let uu____5119 =
                                       let uu___98_5120 = goal  in
                                       let uu____5121 =
                                         FStar_Syntax_Subst.subst s
                                           goal.FStar_Tactics_Types.witness
                                          in
                                       let uu____5122 =
                                         FStar_Syntax_Subst.subst s
                                           goal.FStar_Tactics_Types.goal_ty
                                          in
                                       {
                                         FStar_Tactics_Types.context = env';
                                         FStar_Tactics_Types.witness =
                                           uu____5121;
                                         FStar_Tactics_Types.goal_ty =
                                           uu____5122;
                                         FStar_Tactics_Types.opts =
                                           (uu___98_5120.FStar_Tactics_Types.opts);
                                         FStar_Tactics_Types.is_guard =
                                           (uu___98_5120.FStar_Tactics_Types.is_guard)
                                       }  in
                                     [uu____5119]  in
                                   add_goals uu____5116  in
                                 bind uu____5113
                                   (fun uu____5125  ->
                                      let uu____5126 =
                                        FStar_Syntax_Util.mk_eq2
                                          (FStar_Syntax_Syntax.U_succ u) ty
                                          bv.FStar_Syntax_Syntax.sort t'
                                         in
                                      add_irrelevant_goal
                                        "binder_retype equation" e0
                                        uu____5126
                                        goal.FStar_Tactics_Types.opts))))))
  
let (norm_binder_type :
  FStar_Syntax_Embeddings.norm_step Prims.list ->
    FStar_Syntax_Syntax.binder -> Prims.unit tac)
  =
  fun s  ->
    fun b  ->
      bind cur_goal
        (fun goal  ->
           let uu____5147 = b  in
           match uu____5147 with
           | (bv,uu____5151) ->
               let uu____5152 = split_env bv goal.FStar_Tactics_Types.context
                  in
               (match uu____5152 with
                | FStar_Pervasives_Native.None  ->
                    fail
                      "binder_retype: binder is not present in environment"
                | FStar_Pervasives_Native.Some (e0,bvs) ->
                    let steps =
                      let uu____5184 =
                        FStar_TypeChecker_Normalize.tr_norm_steps s  in
                      FStar_List.append
                        [FStar_TypeChecker_Normalize.Reify;
                        FStar_TypeChecker_Normalize.UnfoldTac] uu____5184
                       in
                    let sort' =
                      normalize steps e0 bv.FStar_Syntax_Syntax.sort  in
                    let bv' =
                      let uu___99_5189 = bv  in
                      {
                        FStar_Syntax_Syntax.ppname =
                          (uu___99_5189.FStar_Syntax_Syntax.ppname);
                        FStar_Syntax_Syntax.index =
                          (uu___99_5189.FStar_Syntax_Syntax.index);
                        FStar_Syntax_Syntax.sort = sort'
                      }  in
                    let env' = push_bvs e0 (bv' :: bvs)  in
                    replace_cur
                      (let uu___100_5193 = goal  in
                       {
                         FStar_Tactics_Types.context = env';
                         FStar_Tactics_Types.witness =
                           (uu___100_5193.FStar_Tactics_Types.witness);
                         FStar_Tactics_Types.goal_ty =
                           (uu___100_5193.FStar_Tactics_Types.goal_ty);
                         FStar_Tactics_Types.opts =
                           (uu___100_5193.FStar_Tactics_Types.opts);
                         FStar_Tactics_Types.is_guard =
                           (uu___100_5193.FStar_Tactics_Types.is_guard)
                       })))
  
let (revert : Prims.unit tac) =
  bind cur_goal
    (fun goal  ->
       let uu____5201 =
         FStar_TypeChecker_Env.pop_bv goal.FStar_Tactics_Types.context  in
       match uu____5201 with
       | FStar_Pervasives_Native.None  -> fail "Cannot revert; empty context"
       | FStar_Pervasives_Native.Some (x,env') ->
           let typ' =
             let uu____5223 =
               FStar_Syntax_Syntax.mk_Total goal.FStar_Tactics_Types.goal_ty
                in
             FStar_Syntax_Util.arrow [(x, FStar_Pervasives_Native.None)]
               uu____5223
              in
           let w' =
             FStar_Syntax_Util.abs [(x, FStar_Pervasives_Native.None)]
               goal.FStar_Tactics_Types.witness FStar_Pervasives_Native.None
              in
           replace_cur
             (let uu___101_5257 = goal  in
              {
                FStar_Tactics_Types.context = env';
                FStar_Tactics_Types.witness = w';
                FStar_Tactics_Types.goal_ty = typ';
                FStar_Tactics_Types.opts =
                  (uu___101_5257.FStar_Tactics_Types.opts);
                FStar_Tactics_Types.is_guard =
                  (uu___101_5257.FStar_Tactics_Types.is_guard)
              }))
  
let (free_in :
  FStar_Syntax_Syntax.bv -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun bv  ->
    fun t  ->
      let uu____5264 = FStar_Syntax_Free.names t  in
      FStar_Util.set_mem bv uu____5264
  
let rec (clear : FStar_Syntax_Syntax.binder -> Prims.unit tac) =
  fun b  ->
    let bv = FStar_Pervasives_Native.fst b  in
    bind cur_goal
      (fun goal  ->
         mlog
           (fun uu____5280  ->
              let uu____5281 = FStar_Syntax_Print.binder_to_string b  in
              let uu____5282 =
                let uu____5283 =
                  let uu____5284 =
                    FStar_TypeChecker_Env.all_binders
                      goal.FStar_Tactics_Types.context
                     in
                  FStar_All.pipe_right uu____5284 FStar_List.length  in
                FStar_All.pipe_right uu____5283 FStar_Util.string_of_int  in
              FStar_Util.print2 "Clear of (%s), env has %s binders\n"
                uu____5281 uu____5282)
           (fun uu____5295  ->
              let uu____5296 = split_env bv goal.FStar_Tactics_Types.context
                 in
              match uu____5296 with
              | FStar_Pervasives_Native.None  ->
                  fail "Cannot clear; binder not in environment"
              | FStar_Pervasives_Native.Some (e',bvs) ->
                  let rec check1 bvs1 =
                    match bvs1 with
                    | [] -> ret ()
                    | bv'::bvs2 ->
                        let uu____5341 =
                          free_in bv bv'.FStar_Syntax_Syntax.sort  in
                        if uu____5341
                        then
                          let uu____5344 =
                            let uu____5345 =
                              FStar_Syntax_Print.bv_to_string bv'  in
                            FStar_Util.format1
                              "Cannot clear; binder present in the type of %s"
                              uu____5345
                             in
                          fail uu____5344
                        else check1 bvs2
                     in
                  let uu____5347 =
                    free_in bv goal.FStar_Tactics_Types.goal_ty  in
                  if uu____5347
                  then fail "Cannot clear; binder present in goal"
                  else
                    (let uu____5351 = check1 bvs  in
                     bind uu____5351
                       (fun uu____5357  ->
                          let env' = push_bvs e' bvs  in
                          let uu____5359 =
                            new_uvar "clear.witness" env'
                              goal.FStar_Tactics_Types.goal_ty
                             in
                          bind uu____5359
                            (fun ut  ->
                               let uu____5365 =
                                 do_unify goal.FStar_Tactics_Types.context
                                   goal.FStar_Tactics_Types.witness ut
                                  in
                               bind uu____5365
                                 (fun b1  ->
                                    if b1
                                    then
                                      replace_cur
                                        (let uu___102_5374 = goal  in
                                         {
                                           FStar_Tactics_Types.context = env';
                                           FStar_Tactics_Types.witness = ut;
                                           FStar_Tactics_Types.goal_ty =
                                             (uu___102_5374.FStar_Tactics_Types.goal_ty);
                                           FStar_Tactics_Types.opts =
                                             (uu___102_5374.FStar_Tactics_Types.opts);
                                           FStar_Tactics_Types.is_guard =
                                             (uu___102_5374.FStar_Tactics_Types.is_guard)
                                         })
                                    else
                                      fail
                                        "Cannot clear; binder appears in witness"))))))
  
let (clear_top : Prims.unit tac) =
  bind cur_goal
    (fun goal  ->
       let uu____5383 =
         FStar_TypeChecker_Env.pop_bv goal.FStar_Tactics_Types.context  in
       match uu____5383 with
       | FStar_Pervasives_Native.None  -> fail "Cannot clear; empty context"
       | FStar_Pervasives_Native.Some (x,uu____5397) ->
           let uu____5402 = FStar_Syntax_Syntax.mk_binder x  in
           clear uu____5402)
  
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
           let uu___103_5418 = g  in
           {
             FStar_Tactics_Types.context = ctx';
             FStar_Tactics_Types.witness =
               (uu___103_5418.FStar_Tactics_Types.witness);
             FStar_Tactics_Types.goal_ty =
               (uu___103_5418.FStar_Tactics_Types.goal_ty);
             FStar_Tactics_Types.opts =
               (uu___103_5418.FStar_Tactics_Types.opts);
             FStar_Tactics_Types.is_guard =
               (uu___103_5418.FStar_Tactics_Types.is_guard)
           }  in
         bind __dismiss (fun uu____5420  -> add_goals [g']))
  
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
           let uu___104_5436 = g  in
           {
             FStar_Tactics_Types.context = ctx';
             FStar_Tactics_Types.witness =
               (uu___104_5436.FStar_Tactics_Types.witness);
             FStar_Tactics_Types.goal_ty =
               (uu___104_5436.FStar_Tactics_Types.goal_ty);
             FStar_Tactics_Types.opts =
               (uu___104_5436.FStar_Tactics_Types.opts);
             FStar_Tactics_Types.is_guard =
               (uu___104_5436.FStar_Tactics_Types.is_guard)
           }  in
         bind __dismiss (fun uu____5438  -> add_goals [g']))
  
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
            let uu____5470 = FStar_Syntax_Subst.compress t  in
            uu____5470.FStar_Syntax_Syntax.n  in
          let uu____5473 =
            if d = FStar_Tactics_Types.TopDown
            then
              f env
                (let uu___108_5479 = t  in
                 {
                   FStar_Syntax_Syntax.n = tn;
                   FStar_Syntax_Syntax.pos =
                     (uu___108_5479.FStar_Syntax_Syntax.pos);
                   FStar_Syntax_Syntax.vars =
                     (uu___108_5479.FStar_Syntax_Syntax.vars)
                 })
            else ret t  in
          bind uu____5473
            (fun t1  ->
               let ff = tac_fold_env d f env  in
               let tn1 =
                 let uu____5493 =
                   let uu____5494 = FStar_Syntax_Subst.compress t1  in
                   uu____5494.FStar_Syntax_Syntax.n  in
                 match uu____5493 with
                 | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
                     let uu____5521 = ff hd1  in
                     bind uu____5521
                       (fun hd2  ->
                          let fa uu____5541 =
                            match uu____5541 with
                            | (a,q) ->
                                let uu____5554 = ff a  in
                                bind uu____5554 (fun a1  -> ret (a1, q))
                             in
                          let uu____5567 = mapM fa args  in
                          bind uu____5567
                            (fun args1  ->
                               ret (FStar_Syntax_Syntax.Tm_app (hd2, args1))))
                 | FStar_Syntax_Syntax.Tm_abs (bs,t2,k) ->
                     let uu____5627 = FStar_Syntax_Subst.open_term bs t2  in
                     (match uu____5627 with
                      | (bs1,t') ->
                          let uu____5636 =
                            let uu____5639 =
                              FStar_TypeChecker_Env.push_binders env bs1  in
                            tac_fold_env d f uu____5639 t'  in
                          bind uu____5636
                            (fun t''  ->
                               let uu____5643 =
                                 let uu____5644 =
                                   let uu____5661 =
                                     FStar_Syntax_Subst.close_binders bs1  in
                                   let uu____5662 =
                                     FStar_Syntax_Subst.close bs1 t''  in
                                   (uu____5661, uu____5662, k)  in
                                 FStar_Syntax_Syntax.Tm_abs uu____5644  in
                               ret uu____5643))
                 | FStar_Syntax_Syntax.Tm_arrow (bs,k) -> ret tn
                 | FStar_Syntax_Syntax.Tm_match (hd1,brs) ->
                     let uu____5721 = ff hd1  in
                     bind uu____5721
                       (fun hd2  ->
                          let ffb br =
                            let uu____5734 =
                              FStar_Syntax_Subst.open_branch br  in
                            match uu____5734 with
                            | (pat,w,e) ->
                                let uu____5756 = ff e  in
                                bind uu____5756
                                  (fun e1  ->
                                     let br1 =
                                       FStar_Syntax_Subst.close_branch
                                         (pat, w, e1)
                                        in
                                     ret br1)
                             in
                          let uu____5769 = mapM ffb brs  in
                          bind uu____5769
                            (fun brs1  ->
                               ret (FStar_Syntax_Syntax.Tm_match (hd2, brs1))))
                 | FStar_Syntax_Syntax.Tm_let
                     ((false
                       ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl bv;
                          FStar_Syntax_Syntax.lbunivs = uu____5783;
                          FStar_Syntax_Syntax.lbtyp = uu____5784;
                          FStar_Syntax_Syntax.lbeff = uu____5785;
                          FStar_Syntax_Syntax.lbdef = def;
                          FStar_Syntax_Syntax.lbattrs = uu____5787;
                          FStar_Syntax_Syntax.lbpos = uu____5788;_}::[]),e)
                     ->
                     let lb =
                       let uu____5813 =
                         let uu____5814 = FStar_Syntax_Subst.compress t1  in
                         uu____5814.FStar_Syntax_Syntax.n  in
                       match uu____5813 with
                       | FStar_Syntax_Syntax.Tm_let
                           ((false ,lb::[]),uu____5818) -> lb
                       | uu____5831 -> failwith "impossible"  in
                     let fflb lb1 =
                       let uu____5838 = ff lb1.FStar_Syntax_Syntax.lbdef  in
                       bind uu____5838
                         (fun def1  ->
                            ret
                              (let uu___105_5844 = lb1  in
                               {
                                 FStar_Syntax_Syntax.lbname =
                                   (uu___105_5844.FStar_Syntax_Syntax.lbname);
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___105_5844.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp =
                                   (uu___105_5844.FStar_Syntax_Syntax.lbtyp);
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___105_5844.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def1;
                                 FStar_Syntax_Syntax.lbattrs =
                                   (uu___105_5844.FStar_Syntax_Syntax.lbattrs);
                                 FStar_Syntax_Syntax.lbpos =
                                   (uu___105_5844.FStar_Syntax_Syntax.lbpos)
                               }))
                        in
                     let uu____5845 = fflb lb  in
                     bind uu____5845
                       (fun lb1  ->
                          let uu____5854 =
                            let uu____5859 =
                              let uu____5860 =
                                FStar_Syntax_Syntax.mk_binder bv  in
                              [uu____5860]  in
                            FStar_Syntax_Subst.open_term uu____5859 e  in
                          match uu____5854 with
                          | (bs,e1) ->
                              let uu____5865 = ff e1  in
                              bind uu____5865
                                (fun e2  ->
                                   let e3 = FStar_Syntax_Subst.close bs e2
                                      in
                                   ret
                                     (FStar_Syntax_Syntax.Tm_let
                                        ((false, [lb1]), e3))))
                 | FStar_Syntax_Syntax.Tm_let ((true ,lbs),e) ->
                     let fflb lb =
                       let uu____5902 = ff lb.FStar_Syntax_Syntax.lbdef  in
                       bind uu____5902
                         (fun def  ->
                            ret
                              (let uu___106_5908 = lb  in
                               {
                                 FStar_Syntax_Syntax.lbname =
                                   (uu___106_5908.FStar_Syntax_Syntax.lbname);
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___106_5908.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp =
                                   (uu___106_5908.FStar_Syntax_Syntax.lbtyp);
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___106_5908.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def;
                                 FStar_Syntax_Syntax.lbattrs =
                                   (uu___106_5908.FStar_Syntax_Syntax.lbattrs);
                                 FStar_Syntax_Syntax.lbpos =
                                   (uu___106_5908.FStar_Syntax_Syntax.lbpos)
                               }))
                        in
                     let uu____5909 = FStar_Syntax_Subst.open_let_rec lbs e
                        in
                     (match uu____5909 with
                      | (lbs1,e1) ->
                          let uu____5924 = mapM fflb lbs1  in
                          bind uu____5924
                            (fun lbs2  ->
                               let uu____5936 = ff e1  in
                               bind uu____5936
                                 (fun e2  ->
                                    let uu____5944 =
                                      FStar_Syntax_Subst.close_let_rec lbs2
                                        e2
                                       in
                                    match uu____5944 with
                                    | (lbs3,e3) ->
                                        ret
                                          (FStar_Syntax_Syntax.Tm_let
                                             ((true, lbs3), e3)))))
                 | FStar_Syntax_Syntax.Tm_ascribed (t2,asc,eff) ->
                     let uu____6010 = ff t2  in
                     bind uu____6010
                       (fun t3  ->
                          ret
                            (FStar_Syntax_Syntax.Tm_ascribed (t3, asc, eff)))
                 | FStar_Syntax_Syntax.Tm_meta (t2,m) ->
                     let uu____6039 = ff t2  in
                     bind uu____6039
                       (fun t3  -> ret (FStar_Syntax_Syntax.Tm_meta (t3, m)))
                 | uu____6044 -> ret tn  in
               bind tn1
                 (fun tn2  ->
                    let t' =
                      let uu___107_6051 = t1  in
                      {
                        FStar_Syntax_Syntax.n = tn2;
                        FStar_Syntax_Syntax.pos =
                          (uu___107_6051.FStar_Syntax_Syntax.pos);
                        FStar_Syntax_Syntax.vars =
                          (uu___107_6051.FStar_Syntax_Syntax.vars)
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
            let uu____6080 = FStar_TypeChecker_TcTerm.tc_term env t  in
            match uu____6080 with
            | (t1,lcomp,g) ->
                let uu____6092 =
                  (let uu____6095 =
                     FStar_Syntax_Util.is_pure_or_ghost_lcomp lcomp  in
                   Prims.op_Negation uu____6095) ||
                    (let uu____6097 = FStar_TypeChecker_Rel.is_trivial g  in
                     Prims.op_Negation uu____6097)
                   in
                if uu____6092
                then ret t1
                else
                  (let rewrite_eq =
                     let typ = lcomp.FStar_Syntax_Syntax.res_typ  in
                     let uu____6107 = new_uvar "pointwise_rec" env typ  in
                     bind uu____6107
                       (fun ut  ->
                          log ps
                            (fun uu____6118  ->
                               let uu____6119 =
                                 FStar_Syntax_Print.term_to_string t1  in
                               let uu____6120 =
                                 FStar_Syntax_Print.term_to_string ut  in
                               FStar_Util.print2
                                 "Pointwise_rec: making equality\n\t%s ==\n\t%s\n"
                                 uu____6119 uu____6120);
                          (let uu____6121 =
                             let uu____6124 =
                               let uu____6125 =
                                 FStar_TypeChecker_TcTerm.universe_of env typ
                                  in
                               FStar_Syntax_Util.mk_eq2 uu____6125 typ t1 ut
                                in
                             add_irrelevant_goal "pointwise_rec equation" env
                               uu____6124 opts
                              in
                           bind uu____6121
                             (fun uu____6128  ->
                                let uu____6129 =
                                  bind tau
                                    (fun uu____6135  ->
                                       let ut1 =
                                         FStar_TypeChecker_Normalize.reduce_uvar_solutions
                                           env ut
                                          in
                                       log ps
                                         (fun uu____6141  ->
                                            let uu____6142 =
                                              FStar_Syntax_Print.term_to_string
                                                t1
                                               in
                                            let uu____6143 =
                                              FStar_Syntax_Print.term_to_string
                                                ut1
                                               in
                                            FStar_Util.print2
                                              "Pointwise_rec: succeeded rewriting\n\t%s to\n\t%s\n"
                                              uu____6142 uu____6143);
                                       ret ut1)
                                   in
                                focus uu____6129)))
                      in
                   let uu____6144 = trytac' rewrite_eq  in
                   bind uu____6144
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
          let uu____6292 = FStar_Syntax_Subst.compress t  in
          maybe_continue ctrl uu____6292
            (fun t1  ->
               let uu____6296 =
                 f env
                   (let uu___111_6305 = t1  in
                    {
                      FStar_Syntax_Syntax.n = (t1.FStar_Syntax_Syntax.n);
                      FStar_Syntax_Syntax.pos =
                        (uu___111_6305.FStar_Syntax_Syntax.pos);
                      FStar_Syntax_Syntax.vars =
                        (uu___111_6305.FStar_Syntax_Syntax.vars)
                    })
                  in
               bind uu____6296
                 (fun uu____6317  ->
                    match uu____6317 with
                    | (t2,ctrl1) ->
                        maybe_continue ctrl1 t2
                          (fun t3  ->
                             let uu____6336 =
                               let uu____6337 =
                                 FStar_Syntax_Subst.compress t3  in
                               uu____6337.FStar_Syntax_Syntax.n  in
                             match uu____6336 with
                             | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
                                 let uu____6370 =
                                   ctrl_tac_fold f env ctrl1 hd1  in
                                 bind uu____6370
                                   (fun uu____6395  ->
                                      match uu____6395 with
                                      | (hd2,ctrl2) ->
                                          let ctrl3 = keep_going ctrl2  in
                                          let uu____6411 =
                                            ctrl_tac_fold_args f env ctrl3
                                              args
                                             in
                                          bind uu____6411
                                            (fun uu____6438  ->
                                               match uu____6438 with
                                               | (args1,ctrl4) ->
                                                   ret
                                                     ((let uu___109_6468 = t3
                                                          in
                                                       {
                                                         FStar_Syntax_Syntax.n
                                                           =
                                                           (FStar_Syntax_Syntax.Tm_app
                                                              (hd2, args1));
                                                         FStar_Syntax_Syntax.pos
                                                           =
                                                           (uu___109_6468.FStar_Syntax_Syntax.pos);
                                                         FStar_Syntax_Syntax.vars
                                                           =
                                                           (uu___109_6468.FStar_Syntax_Syntax.vars)
                                                       }), ctrl4)))
                             | FStar_Syntax_Syntax.Tm_abs (bs,t4,k) ->
                                 let uu____6494 =
                                   FStar_Syntax_Subst.open_term bs t4  in
                                 (match uu____6494 with
                                  | (bs1,t') ->
                                      let uu____6509 =
                                        let uu____6516 =
                                          FStar_TypeChecker_Env.push_binders
                                            env bs1
                                           in
                                        ctrl_tac_fold f uu____6516 ctrl1 t'
                                         in
                                      bind uu____6509
                                        (fun uu____6534  ->
                                           match uu____6534 with
                                           | (t'',ctrl2) ->
                                               let uu____6549 =
                                                 let uu____6556 =
                                                   let uu___110_6559 = t4  in
                                                   let uu____6562 =
                                                     let uu____6563 =
                                                       let uu____6580 =
                                                         FStar_Syntax_Subst.close_binders
                                                           bs1
                                                          in
                                                       let uu____6581 =
                                                         FStar_Syntax_Subst.close
                                                           bs1 t''
                                                          in
                                                       (uu____6580,
                                                         uu____6581, k)
                                                        in
                                                     FStar_Syntax_Syntax.Tm_abs
                                                       uu____6563
                                                      in
                                                   {
                                                     FStar_Syntax_Syntax.n =
                                                       uu____6562;
                                                     FStar_Syntax_Syntax.pos
                                                       =
                                                       (uu___110_6559.FStar_Syntax_Syntax.pos);
                                                     FStar_Syntax_Syntax.vars
                                                       =
                                                       (uu___110_6559.FStar_Syntax_Syntax.vars)
                                                   }  in
                                                 (uu____6556, ctrl2)  in
                                               ret uu____6549))
                             | FStar_Syntax_Syntax.Tm_arrow (bs,k) ->
                                 ret (t3, ctrl1)
                             | uu____6614 -> ret (t3, ctrl1))))

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
              let uu____6665 = ctrl_tac_fold f env ctrl t  in
              bind uu____6665
                (fun uu____6693  ->
                   match uu____6693 with
                   | (t1,ctrl1) ->
                       let uu____6712 = ctrl_tac_fold_args f env ctrl1 ts1
                          in
                       bind uu____6712
                         (fun uu____6743  ->
                            match uu____6743 with
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
              let uu____6827 =
                let uu____6834 =
                  add_irrelevant_goal "dummy" env FStar_Syntax_Util.t_true
                    opts
                   in
                bind uu____6834
                  (fun uu____6843  ->
                     let uu____6844 = ctrl t1  in
                     bind uu____6844
                       (fun res  -> bind trivial (fun uu____6871  -> ret res)))
                 in
              bind uu____6827
                (fun uu____6887  ->
                   match uu____6887 with
                   | (should_rewrite,ctrl1) ->
                       if Prims.op_Negation should_rewrite
                       then ret (t1, ctrl1)
                       else
                         (let uu____6911 =
                            FStar_TypeChecker_TcTerm.tc_term env t1  in
                          match uu____6911 with
                          | (t2,lcomp,g) ->
                              let uu____6927 =
                                (let uu____6930 =
                                   FStar_Syntax_Util.is_pure_or_ghost_lcomp
                                     lcomp
                                    in
                                 Prims.op_Negation uu____6930) ||
                                  (let uu____6932 =
                                     FStar_TypeChecker_Rel.is_trivial g  in
                                   Prims.op_Negation uu____6932)
                                 in
                              if uu____6927
                              then ret (t2, globalStop)
                              else
                                (let typ = lcomp.FStar_Syntax_Syntax.res_typ
                                    in
                                 let uu____6947 =
                                   new_uvar "pointwise_rec" env typ  in
                                 bind uu____6947
                                   (fun ut  ->
                                      log ps
                                        (fun uu____6962  ->
                                           let uu____6963 =
                                             FStar_Syntax_Print.term_to_string
                                               t2
                                              in
                                           let uu____6964 =
                                             FStar_Syntax_Print.term_to_string
                                               ut
                                              in
                                           FStar_Util.print2
                                             "Pointwise_rec: making equality\n\t%s ==\n\t%s\n"
                                             uu____6963 uu____6964);
                                      (let uu____6965 =
                                         let uu____6968 =
                                           let uu____6969 =
                                             FStar_TypeChecker_TcTerm.universe_of
                                               env typ
                                              in
                                           FStar_Syntax_Util.mk_eq2
                                             uu____6969 typ t2 ut
                                            in
                                         add_irrelevant_goal
                                           "rewrite_rec equation" env
                                           uu____6968 opts
                                          in
                                       bind uu____6965
                                         (fun uu____6976  ->
                                            let uu____6977 =
                                              bind rewriter
                                                (fun uu____6991  ->
                                                   let ut1 =
                                                     FStar_TypeChecker_Normalize.reduce_uvar_solutions
                                                       env ut
                                                      in
                                                   log ps
                                                     (fun uu____6997  ->
                                                        let uu____6998 =
                                                          FStar_Syntax_Print.term_to_string
                                                            t2
                                                           in
                                                        let uu____6999 =
                                                          FStar_Syntax_Print.term_to_string
                                                            ut1
                                                           in
                                                        FStar_Util.print2
                                                          "rewrite_rec: succeeded rewriting\n\t%s to\n\t%s\n"
                                                          uu____6998
                                                          uu____6999);
                                                   ret (ut1, ctrl1))
                                               in
                                            focus uu____6977))))))
  
let (topdown_rewrite :
  (FStar_Syntax_Syntax.term ->
     (Prims.bool,FStar_BigInt.t) FStar_Pervasives_Native.tuple2 tac)
    -> Prims.unit tac -> Prims.unit tac)
  =
  fun ctrl  ->
    fun rewriter  ->
      bind get
        (fun ps  ->
           let uu____7043 =
             match ps.FStar_Tactics_Types.goals with
             | g::gs -> (g, gs)
             | [] -> failwith "Pointwise: no goals"  in
           match uu____7043 with
           | (g,gs) ->
               let gt1 = g.FStar_Tactics_Types.goal_ty  in
               (log ps
                  (fun uu____7080  ->
                     let uu____7081 = FStar_Syntax_Print.term_to_string gt1
                        in
                     FStar_Util.print1 "Pointwise starting with %s\n"
                       uu____7081);
                bind dismiss_all
                  (fun uu____7084  ->
                     let uu____7085 =
                       ctrl_tac_fold
                         (rewrite_rec ps ctrl rewriter
                            g.FStar_Tactics_Types.opts)
                         g.FStar_Tactics_Types.context keepGoing gt1
                        in
                     bind uu____7085
                       (fun uu____7103  ->
                          match uu____7103 with
                          | (gt',uu____7111) ->
                              (log ps
                                 (fun uu____7115  ->
                                    let uu____7116 =
                                      FStar_Syntax_Print.term_to_string gt'
                                       in
                                    FStar_Util.print1
                                      "Pointwise seems to have succeded with %s\n"
                                      uu____7116);
                               (let uu____7117 = push_goals gs  in
                                bind uu____7117
                                  (fun uu____7121  ->
                                     add_goals
                                       [(let uu___112_7123 = g  in
                                         {
                                           FStar_Tactics_Types.context =
                                             (uu___112_7123.FStar_Tactics_Types.context);
                                           FStar_Tactics_Types.witness =
                                             (uu___112_7123.FStar_Tactics_Types.witness);
                                           FStar_Tactics_Types.goal_ty = gt';
                                           FStar_Tactics_Types.opts =
                                             (uu___112_7123.FStar_Tactics_Types.opts);
                                           FStar_Tactics_Types.is_guard =
                                             (uu___112_7123.FStar_Tactics_Types.is_guard)
                                         })])))))))
  
let (pointwise :
  FStar_Tactics_Types.direction -> Prims.unit tac -> Prims.unit tac) =
  fun d  ->
    fun tau  ->
      bind get
        (fun ps  ->
           let uu____7145 =
             match ps.FStar_Tactics_Types.goals with
             | g::gs -> (g, gs)
             | [] -> failwith "Pointwise: no goals"  in
           match uu____7145 with
           | (g,gs) ->
               let gt1 = g.FStar_Tactics_Types.goal_ty  in
               (log ps
                  (fun uu____7182  ->
                     let uu____7183 = FStar_Syntax_Print.term_to_string gt1
                        in
                     FStar_Util.print1 "Pointwise starting with %s\n"
                       uu____7183);
                bind dismiss_all
                  (fun uu____7186  ->
                     let uu____7187 =
                       tac_fold_env d
                         (pointwise_rec ps tau g.FStar_Tactics_Types.opts)
                         g.FStar_Tactics_Types.context gt1
                        in
                     bind uu____7187
                       (fun gt'  ->
                          log ps
                            (fun uu____7197  ->
                               let uu____7198 =
                                 FStar_Syntax_Print.term_to_string gt'  in
                               FStar_Util.print1
                                 "Pointwise seems to have succeded with %s\n"
                                 uu____7198);
                          (let uu____7199 = push_goals gs  in
                           bind uu____7199
                             (fun uu____7203  ->
                                add_goals
                                  [(let uu___113_7205 = g  in
                                    {
                                      FStar_Tactics_Types.context =
                                        (uu___113_7205.FStar_Tactics_Types.context);
                                      FStar_Tactics_Types.witness =
                                        (uu___113_7205.FStar_Tactics_Types.witness);
                                      FStar_Tactics_Types.goal_ty = gt';
                                      FStar_Tactics_Types.opts =
                                        (uu___113_7205.FStar_Tactics_Types.opts);
                                      FStar_Tactics_Types.is_guard =
                                        (uu___113_7205.FStar_Tactics_Types.is_guard)
                                    })]))))))
  
let (trefl : Prims.unit tac) =
  bind cur_goal
    (fun g  ->
       let uu____7225 =
         FStar_Syntax_Util.un_squash g.FStar_Tactics_Types.goal_ty  in
       match uu____7225 with
       | FStar_Pervasives_Native.Some t ->
           let uu____7237 = FStar_Syntax_Util.head_and_args' t  in
           (match uu____7237 with
            | (hd1,args) ->
                let uu____7270 =
                  let uu____7283 =
                    let uu____7284 = FStar_Syntax_Util.un_uinst hd1  in
                    uu____7284.FStar_Syntax_Syntax.n  in
                  (uu____7283, args)  in
                (match uu____7270 with
                 | (FStar_Syntax_Syntax.Tm_fvar
                    fv,uu____7298::(l,uu____7300)::(r,uu____7302)::[]) when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.eq2_lid
                     ->
                     let uu____7349 =
                       do_unify g.FStar_Tactics_Types.context l r  in
                     bind uu____7349
                       (fun b  ->
                          if Prims.op_Negation b
                          then
                            let uu____7358 =
                              tts g.FStar_Tactics_Types.context l  in
                            let uu____7359 =
                              tts g.FStar_Tactics_Types.context r  in
                            fail2 "trefl: not a trivial equality (%s vs %s)"
                              uu____7358 uu____7359
                          else solve g FStar_Syntax_Util.exp_unit)
                 | (hd2,uu____7362) ->
                     let uu____7379 = tts g.FStar_Tactics_Types.context t  in
                     fail1 "trefl: not an equality (%s)" uu____7379))
       | FStar_Pervasives_Native.None  -> fail "not an irrelevant goal")
  
let (dup : Prims.unit tac) =
  bind cur_goal
    (fun g  ->
       let uu____7389 =
         new_uvar "dup" g.FStar_Tactics_Types.context
           g.FStar_Tactics_Types.goal_ty
          in
       bind uu____7389
         (fun u  ->
            let g' =
              let uu___114_7396 = g  in
              {
                FStar_Tactics_Types.context =
                  (uu___114_7396.FStar_Tactics_Types.context);
                FStar_Tactics_Types.witness = u;
                FStar_Tactics_Types.goal_ty =
                  (uu___114_7396.FStar_Tactics_Types.goal_ty);
                FStar_Tactics_Types.opts =
                  (uu___114_7396.FStar_Tactics_Types.opts);
                FStar_Tactics_Types.is_guard =
                  (uu___114_7396.FStar_Tactics_Types.is_guard)
              }  in
            bind __dismiss
              (fun uu____7399  ->
                 let uu____7400 =
                   let uu____7403 =
                     let uu____7404 =
                       FStar_TypeChecker_TcTerm.universe_of
                         g.FStar_Tactics_Types.context
                         g.FStar_Tactics_Types.goal_ty
                        in
                     FStar_Syntax_Util.mk_eq2 uu____7404
                       g.FStar_Tactics_Types.goal_ty u
                       g.FStar_Tactics_Types.witness
                      in
                   add_irrelevant_goal "dup equation"
                     g.FStar_Tactics_Types.context uu____7403
                     g.FStar_Tactics_Types.opts
                    in
                 bind uu____7400
                   (fun uu____7407  ->
                      let uu____7408 = add_goals [g']  in
                      bind uu____7408 (fun uu____7412  -> ret ())))))
  
let (flip : Prims.unit tac) =
  bind get
    (fun ps  ->
       match ps.FStar_Tactics_Types.goals with
       | g1::g2::gs ->
           set
             (let uu___115_7431 = ps  in
              {
                FStar_Tactics_Types.main_context =
                  (uu___115_7431.FStar_Tactics_Types.main_context);
                FStar_Tactics_Types.main_goal =
                  (uu___115_7431.FStar_Tactics_Types.main_goal);
                FStar_Tactics_Types.all_implicits =
                  (uu___115_7431.FStar_Tactics_Types.all_implicits);
                FStar_Tactics_Types.goals = (g2 :: g1 :: gs);
                FStar_Tactics_Types.smt_goals =
                  (uu___115_7431.FStar_Tactics_Types.smt_goals);
                FStar_Tactics_Types.depth =
                  (uu___115_7431.FStar_Tactics_Types.depth);
                FStar_Tactics_Types.__dump =
                  (uu___115_7431.FStar_Tactics_Types.__dump);
                FStar_Tactics_Types.psc =
                  (uu___115_7431.FStar_Tactics_Types.psc);
                FStar_Tactics_Types.entry_range =
                  (uu___115_7431.FStar_Tactics_Types.entry_range);
                FStar_Tactics_Types.guard_policy =
                  (uu___115_7431.FStar_Tactics_Types.guard_policy)
              })
       | uu____7432 -> fail "flip: less than 2 goals")
  
let (later : Prims.unit tac) =
  bind get
    (fun ps  ->
       match ps.FStar_Tactics_Types.goals with
       | [] -> ret ()
       | g::gs ->
           set
             (let uu___116_7449 = ps  in
              {
                FStar_Tactics_Types.main_context =
                  (uu___116_7449.FStar_Tactics_Types.main_context);
                FStar_Tactics_Types.main_goal =
                  (uu___116_7449.FStar_Tactics_Types.main_goal);
                FStar_Tactics_Types.all_implicits =
                  (uu___116_7449.FStar_Tactics_Types.all_implicits);
                FStar_Tactics_Types.goals = (FStar_List.append gs [g]);
                FStar_Tactics_Types.smt_goals =
                  (uu___116_7449.FStar_Tactics_Types.smt_goals);
                FStar_Tactics_Types.depth =
                  (uu___116_7449.FStar_Tactics_Types.depth);
                FStar_Tactics_Types.__dump =
                  (uu___116_7449.FStar_Tactics_Types.__dump);
                FStar_Tactics_Types.psc =
                  (uu___116_7449.FStar_Tactics_Types.psc);
                FStar_Tactics_Types.entry_range =
                  (uu___116_7449.FStar_Tactics_Types.entry_range);
                FStar_Tactics_Types.guard_policy =
                  (uu___116_7449.FStar_Tactics_Types.guard_policy)
              }))
  
let (qed : Prims.unit tac) =
  bind get
    (fun ps  ->
       match ps.FStar_Tactics_Types.goals with
       | [] -> ret ()
       | uu____7458 -> fail "Not done!")
  
let (cases :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 tac)
  =
  fun t  ->
    let uu____7476 =
      bind cur_goal
        (fun g  ->
           let uu____7490 = __tc g.FStar_Tactics_Types.context t  in
           bind uu____7490
             (fun uu____7526  ->
                match uu____7526 with
                | (t1,typ,guard) ->
                    let uu____7542 = FStar_Syntax_Util.head_and_args typ  in
                    (match uu____7542 with
                     | (hd1,args) ->
                         let uu____7585 =
                           let uu____7598 =
                             let uu____7599 = FStar_Syntax_Util.un_uinst hd1
                                in
                             uu____7599.FStar_Syntax_Syntax.n  in
                           (uu____7598, args)  in
                         (match uu____7585 with
                          | (FStar_Syntax_Syntax.Tm_fvar
                             fv,(p,uu____7618)::(q,uu____7620)::[]) when
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
                                let uu___117_7658 = g  in
                                let uu____7659 =
                                  FStar_TypeChecker_Env.push_bv
                                    g.FStar_Tactics_Types.context v_p
                                   in
                                {
                                  FStar_Tactics_Types.context = uu____7659;
                                  FStar_Tactics_Types.witness =
                                    (uu___117_7658.FStar_Tactics_Types.witness);
                                  FStar_Tactics_Types.goal_ty =
                                    (uu___117_7658.FStar_Tactics_Types.goal_ty);
                                  FStar_Tactics_Types.opts =
                                    (uu___117_7658.FStar_Tactics_Types.opts);
                                  FStar_Tactics_Types.is_guard =
                                    (uu___117_7658.FStar_Tactics_Types.is_guard)
                                }  in
                              let g2 =
                                let uu___118_7661 = g  in
                                let uu____7662 =
                                  FStar_TypeChecker_Env.push_bv
                                    g.FStar_Tactics_Types.context v_q
                                   in
                                {
                                  FStar_Tactics_Types.context = uu____7662;
                                  FStar_Tactics_Types.witness =
                                    (uu___118_7661.FStar_Tactics_Types.witness);
                                  FStar_Tactics_Types.goal_ty =
                                    (uu___118_7661.FStar_Tactics_Types.goal_ty);
                                  FStar_Tactics_Types.opts =
                                    (uu___118_7661.FStar_Tactics_Types.opts);
                                  FStar_Tactics_Types.is_guard =
                                    (uu___118_7661.FStar_Tactics_Types.is_guard)
                                }  in
                              bind __dismiss
                                (fun uu____7669  ->
                                   let uu____7670 = add_goals [g1; g2]  in
                                   bind uu____7670
                                     (fun uu____7679  ->
                                        let uu____7680 =
                                          let uu____7685 =
                                            FStar_Syntax_Syntax.bv_to_name
                                              v_p
                                             in
                                          let uu____7686 =
                                            FStar_Syntax_Syntax.bv_to_name
                                              v_q
                                             in
                                          (uu____7685, uu____7686)  in
                                        ret uu____7680))
                          | uu____7691 ->
                              let uu____7704 =
                                tts g.FStar_Tactics_Types.context typ  in
                              fail1 "Not a disjunction: %s" uu____7704))))
       in
    FStar_All.pipe_left (wrap_err "cases") uu____7476
  
let (set_options : Prims.string -> Prims.unit tac) =
  fun s  ->
    bind cur_goal
      (fun g  ->
         FStar_Options.push ();
         (let uu____7742 = FStar_Util.smap_copy g.FStar_Tactics_Types.opts
             in
          FStar_Options.set uu____7742);
         (let res = FStar_Options.set_options FStar_Options.Set s  in
          let opts' = FStar_Options.peek ()  in
          FStar_Options.pop ();
          (match res with
           | FStar_Getopt.Success  ->
               let g' =
                 let uu___119_7749 = g  in
                 {
                   FStar_Tactics_Types.context =
                     (uu___119_7749.FStar_Tactics_Types.context);
                   FStar_Tactics_Types.witness =
                     (uu___119_7749.FStar_Tactics_Types.witness);
                   FStar_Tactics_Types.goal_ty =
                     (uu___119_7749.FStar_Tactics_Types.goal_ty);
                   FStar_Tactics_Types.opts = opts';
                   FStar_Tactics_Types.is_guard =
                     (uu___119_7749.FStar_Tactics_Types.is_guard)
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
      let uu____7793 =
        bind cur_goal
          (fun goal  ->
             let env =
               FStar_TypeChecker_Env.set_expected_typ
                 goal.FStar_Tactics_Types.context ty
                in
             let uu____7801 = __tc env tm  in
             bind uu____7801
               (fun uu____7821  ->
                  match uu____7821 with
                  | (tm1,typ,guard) ->
                      let uu____7833 =
                        proc_guard "unquote" env guard
                          goal.FStar_Tactics_Types.opts
                         in
                      bind uu____7833 (fun uu____7837  -> ret tm1)))
         in
      FStar_All.pipe_left (wrap_err "unquote") uu____7793
  
let (uvar_env :
  env ->
    FStar_Syntax_Syntax.typ FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.term tac)
  =
  fun env  ->
    fun ty  ->
      let uu____7856 =
        match ty with
        | FStar_Pervasives_Native.Some ty1 -> ret ty1
        | FStar_Pervasives_Native.None  ->
            let uu____7862 =
              let uu____7863 = FStar_Syntax_Util.type_u ()  in
              FStar_All.pipe_left FStar_Pervasives_Native.fst uu____7863  in
            new_uvar "uvar_env.2" env uu____7862
         in
      bind uu____7856
        (fun typ  ->
           let uu____7875 = new_uvar "uvar_env" env typ  in
           bind uu____7875 (fun t  -> ret t))
  
let (unshelve : FStar_Syntax_Syntax.term -> Prims.unit tac) =
  fun t  ->
    let uu____7887 =
      bind get
        (fun ps  ->
           let env = ps.FStar_Tactics_Types.main_context  in
           let opts =
             match ps.FStar_Tactics_Types.goals with
             | g::uu____7898 -> g.FStar_Tactics_Types.opts
             | uu____7901 -> FStar_Options.peek ()  in
           let uu____7904 = __tc env t  in
           bind uu____7904
             (fun uu____7924  ->
                match uu____7924 with
                | (t1,typ,guard) ->
                    let uu____7936 = proc_guard "unshelve" env guard opts  in
                    bind uu____7936
                      (fun uu____7941  ->
                         let uu____7942 =
                           let uu____7945 =
                             let uu____7946 = bnorm env t1  in
                             let uu____7947 = bnorm env typ  in
                             {
                               FStar_Tactics_Types.context = env;
                               FStar_Tactics_Types.witness = uu____7946;
                               FStar_Tactics_Types.goal_ty = uu____7947;
                               FStar_Tactics_Types.opts = opts;
                               FStar_Tactics_Types.is_guard = false
                             }  in
                           [uu____7945]  in
                         add_goals uu____7942)))
       in
    FStar_All.pipe_left (wrap_err "unshelve") uu____7887
  
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
          (fun uu____7980  ->
             let uu____7981 = FStar_Options.unsafe_tactic_exec ()  in
             if uu____7981
             then
               let s =
                 FStar_Util.launch_process true "tactic_launch" prog args
                   input (fun uu____7987  -> fun uu____7988  -> false)
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
        (fun uu____8002  ->
           let uu____8003 =
             FStar_Syntax_Syntax.gen_bv nm FStar_Pervasives_Native.None t  in
           ret uu____8003)
  
let (change : FStar_Syntax_Syntax.typ -> Prims.unit tac) =
  fun ty  ->
    let uu____8011 =
      mlog
        (fun uu____8016  ->
           let uu____8017 = FStar_Syntax_Print.term_to_string ty  in
           FStar_Util.print1 "change: ty = %s\n" uu____8017)
        (fun uu____8019  ->
           bind cur_goal
             (fun g  ->
                let uu____8023 = __tc g.FStar_Tactics_Types.context ty  in
                bind uu____8023
                  (fun uu____8043  ->
                     match uu____8043 with
                     | (ty1,uu____8053,guard) ->
                         let uu____8055 =
                           proc_guard "change" g.FStar_Tactics_Types.context
                             guard g.FStar_Tactics_Types.opts
                            in
                         bind uu____8055
                           (fun uu____8060  ->
                              let uu____8061 =
                                do_unify g.FStar_Tactics_Types.context
                                  g.FStar_Tactics_Types.goal_ty ty1
                                 in
                              bind uu____8061
                                (fun bb  ->
                                   if bb
                                   then
                                     replace_cur
                                       (let uu___120_8070 = g  in
                                        {
                                          FStar_Tactics_Types.context =
                                            (uu___120_8070.FStar_Tactics_Types.context);
                                          FStar_Tactics_Types.witness =
                                            (uu___120_8070.FStar_Tactics_Types.witness);
                                          FStar_Tactics_Types.goal_ty = ty1;
                                          FStar_Tactics_Types.opts =
                                            (uu___120_8070.FStar_Tactics_Types.opts);
                                          FStar_Tactics_Types.is_guard =
                                            (uu___120_8070.FStar_Tactics_Types.is_guard)
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
                                      let uu____8077 =
                                        do_unify
                                          g.FStar_Tactics_Types.context ng
                                          nty
                                         in
                                      bind uu____8077
                                        (fun b  ->
                                           if b
                                           then
                                             replace_cur
                                               (let uu___121_8086 = g  in
                                                {
                                                  FStar_Tactics_Types.context
                                                    =
                                                    (uu___121_8086.FStar_Tactics_Types.context);
                                                  FStar_Tactics_Types.witness
                                                    =
                                                    (uu___121_8086.FStar_Tactics_Types.witness);
                                                  FStar_Tactics_Types.goal_ty
                                                    = ty1;
                                                  FStar_Tactics_Types.opts =
                                                    (uu___121_8086.FStar_Tactics_Types.opts);
                                                  FStar_Tactics_Types.is_guard
                                                    =
                                                    (uu___121_8086.FStar_Tactics_Types.is_guard)
                                                })
                                           else fail "not convertible")))))))
       in
    FStar_All.pipe_left (wrap_err "change") uu____8011
  
let (goal_of_goal_ty :
  env ->
    FStar_Syntax_Syntax.typ ->
      (FStar_Tactics_Types.goal,FStar_TypeChecker_Env.guard_t)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun typ  ->
      let uu____8106 =
        FStar_TypeChecker_Util.new_implicit_var "proofstate_of_goal_ty"
          typ.FStar_Syntax_Syntax.pos env typ
         in
      match uu____8106 with
      | (u,uu____8124,g_u) ->
          let g =
            let uu____8139 = FStar_Options.peek ()  in
            {
              FStar_Tactics_Types.context = env;
              FStar_Tactics_Types.witness = u;
              FStar_Tactics_Types.goal_ty = typ;
              FStar_Tactics_Types.opts = uu____8139;
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
      let uu____8150 = goal_of_goal_ty env typ  in
      match uu____8150 with
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
  