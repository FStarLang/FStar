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
  
let (ngoals : FStar_BigInt.bigint tac) =
  bind get
    (fun ps  ->
       let n1 = FStar_List.length ps.FStar_Tactics_Types.goals  in
       let uu____1480 = FStar_BigInt.of_int_fs n1  in ret uu____1480)
  
let (ngoals_smt : FStar_BigInt.bigint tac) =
  bind get
    (fun ps  ->
       let n1 = FStar_List.length ps.FStar_Tactics_Types.smt_goals  in
       let uu____1496 = FStar_BigInt.of_int_fs n1  in ret uu____1496)
  
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
            let uu____1528 = env.FStar_TypeChecker_Env.universe_of env phi
               in
            FStar_Syntax_Util.mk_squash uu____1528 phi  in
          let uu____1529 = new_uvar reason env typ  in
          bind uu____1529
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
             let uu____1585 =
               (ps.FStar_Tactics_Types.main_context).FStar_TypeChecker_Env.type_of
                 e t
                in
             ret uu____1585
           with
           | FStar_Errors.Err (uu____1612,msg) ->
               let uu____1614 = tts e t  in
               let uu____1615 =
                 let uu____1616 = FStar_TypeChecker_Env.all_binders e  in
                 FStar_All.pipe_right uu____1616
                   (FStar_Syntax_Print.binders_to_string ", ")
                  in
               fail3 "Cannot type %s in context (%s). Error = (%s)"
                 uu____1614 uu____1615 msg
           | FStar_Errors.Error (uu____1623,msg,uu____1625) ->
               let uu____1626 = tts e t  in
               let uu____1627 =
                 let uu____1628 = FStar_TypeChecker_Env.all_binders e  in
                 FStar_All.pipe_right uu____1628
                   (FStar_Syntax_Print.binders_to_string ", ")
                  in
               fail3 "Cannot type %s in context (%s). Error = (%s)"
                 uu____1626 uu____1627 msg)
  
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
           (let uu___72_1662 = ps  in
            {
              FStar_Tactics_Types.main_context =
                (uu___72_1662.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___72_1662.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___72_1662.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___72_1662.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___72_1662.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___72_1662.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___72_1662.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___72_1662.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___72_1662.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy = pol
            }))
  
let with_policy : 'a . FStar_Tactics_Types.guard_policy -> 'a tac -> 'a tac =
  fun pol  ->
    fun t  ->
      bind get_guard_policy
        (fun old_pol  ->
           let uu____1684 = set_guard_policy pol  in
           bind uu____1684
             (fun uu____1688  ->
                bind t
                  (fun r  ->
                     let uu____1692 = set_guard_policy old_pol  in
                     bind uu____1692 (fun uu____1696  -> ret r))))
  
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
          let uu____1713 =
            let uu____1714 = FStar_TypeChecker_Rel.simplify_guard e g  in
            uu____1714.FStar_TypeChecker_Env.guard_f  in
          match uu____1713 with
          | FStar_TypeChecker_Common.Trivial  -> ret ()
          | FStar_TypeChecker_Common.NonTrivial f ->
              let uu____1718 = istrivial e f  in
              if uu____1718
              then ret ()
              else
                bind get
                  (fun ps  ->
                     match ps.FStar_Tactics_Types.guard_policy with
                     | FStar_Tactics_Types.Drop  -> ret ()
                     | FStar_Tactics_Types.Goal  ->
                         let uu____1726 = mk_irrelevant_goal reason e f opts
                            in
                         bind uu____1726
                           (fun goal  ->
                              let goal1 =
                                let uu___73_1733 = goal  in
                                {
                                  FStar_Tactics_Types.context =
                                    (uu___73_1733.FStar_Tactics_Types.context);
                                  FStar_Tactics_Types.witness =
                                    (uu___73_1733.FStar_Tactics_Types.witness);
                                  FStar_Tactics_Types.goal_ty =
                                    (uu___73_1733.FStar_Tactics_Types.goal_ty);
                                  FStar_Tactics_Types.opts =
                                    (uu___73_1733.FStar_Tactics_Types.opts);
                                  FStar_Tactics_Types.is_guard = true
                                }  in
                              push_goals [goal1])
                     | FStar_Tactics_Types.SMT  ->
                         let uu____1734 = mk_irrelevant_goal reason e f opts
                            in
                         bind uu____1734
                           (fun goal  ->
                              let goal1 =
                                let uu___74_1741 = goal  in
                                {
                                  FStar_Tactics_Types.context =
                                    (uu___74_1741.FStar_Tactics_Types.context);
                                  FStar_Tactics_Types.witness =
                                    (uu___74_1741.FStar_Tactics_Types.witness);
                                  FStar_Tactics_Types.goal_ty =
                                    (uu___74_1741.FStar_Tactics_Types.goal_ty);
                                  FStar_Tactics_Types.opts =
                                    (uu___74_1741.FStar_Tactics_Types.opts);
                                  FStar_Tactics_Types.is_guard = true
                                }  in
                              push_smt_goals [goal1])
                     | FStar_Tactics_Types.Force  ->
                         (try
                            let uu____1749 =
                              let uu____1750 =
                                let uu____1751 =
                                  FStar_TypeChecker_Rel.discharge_guard_no_smt
                                    e g
                                   in
                                FStar_All.pipe_left
                                  FStar_TypeChecker_Rel.is_trivial uu____1751
                                 in
                              Prims.op_Negation uu____1750  in
                            if uu____1749
                            then
                              mlog
                                (fun uu____1756  ->
                                   let uu____1757 =
                                     FStar_TypeChecker_Rel.guard_to_string e
                                       g
                                      in
                                   FStar_Util.print1 "guard = %s\n"
                                     uu____1757)
                                (fun uu____1759  ->
                                   fail1 "Forcing the guard failed %s)"
                                     reason)
                            else ret ()
                          with
                          | uu____1766 ->
                              mlog
                                (fun uu____1769  ->
                                   let uu____1770 =
                                     FStar_TypeChecker_Rel.guard_to_string e
                                       g
                                      in
                                   FStar_Util.print1 "guard = %s\n"
                                     uu____1770)
                                (fun uu____1772  ->
                                   fail1 "Forcing the guard failed (%s)"
                                     reason)))
  
let (tc : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.typ tac) =
  fun t  ->
    let uu____1780 =
      bind cur_goal
        (fun goal  ->
           let uu____1786 = __tc goal.FStar_Tactics_Types.context t  in
           bind uu____1786
             (fun uu____1806  ->
                match uu____1806 with
                | (t1,typ,guard) ->
                    let uu____1818 =
                      proc_guard "tc" goal.FStar_Tactics_Types.context guard
                        goal.FStar_Tactics_Types.opts
                       in
                    bind uu____1818 (fun uu____1822  -> ret typ)))
       in
    FStar_All.pipe_left (wrap_err "tc") uu____1780
  
let (add_irrelevant_goal :
  Prims.string ->
    env ->
      FStar_Syntax_Syntax.typ -> FStar_Options.optionstate -> Prims.unit tac)
  =
  fun reason  ->
    fun env  ->
      fun phi  ->
        fun opts  ->
          let uu____1843 = mk_irrelevant_goal reason env phi opts  in
          bind uu____1843 (fun goal  -> add_goals [goal])
  
let (trivial : Prims.unit tac) =
  bind cur_goal
    (fun goal  ->
       let uu____1855 =
         istrivial goal.FStar_Tactics_Types.context
           goal.FStar_Tactics_Types.goal_ty
          in
       if uu____1855
       then solve goal FStar_Syntax_Util.exp_unit
       else
         (let uu____1859 =
            tts goal.FStar_Tactics_Types.context
              goal.FStar_Tactics_Types.goal_ty
             in
          fail1 "Not a trivial goal: %s" uu____1859))
  
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
          let uu____1880 =
            let uu____1881 = FStar_TypeChecker_Rel.simplify_guard e g  in
            uu____1881.FStar_TypeChecker_Env.guard_f  in
          match uu____1880 with
          | FStar_TypeChecker_Common.Trivial  ->
              ret FStar_Pervasives_Native.None
          | FStar_TypeChecker_Common.NonTrivial f ->
              let uu____1889 = istrivial e f  in
              if uu____1889
              then ret FStar_Pervasives_Native.None
              else
                (let uu____1897 = mk_irrelevant_goal reason e f opts  in
                 bind uu____1897
                   (fun goal  ->
                      ret
                        (FStar_Pervasives_Native.Some
                           (let uu___77_1907 = goal  in
                            {
                              FStar_Tactics_Types.context =
                                (uu___77_1907.FStar_Tactics_Types.context);
                              FStar_Tactics_Types.witness =
                                (uu___77_1907.FStar_Tactics_Types.witness);
                              FStar_Tactics_Types.goal_ty =
                                (uu___77_1907.FStar_Tactics_Types.goal_ty);
                              FStar_Tactics_Types.opts =
                                (uu___77_1907.FStar_Tactics_Types.opts);
                              FStar_Tactics_Types.is_guard = true
                            }))))
  
let (smt : Prims.unit tac) =
  bind cur_goal
    (fun g  ->
       let uu____1915 = is_irrelevant g  in
       if uu____1915
       then bind __dismiss (fun uu____1919  -> add_smt_goals [g])
       else
         (let uu____1921 =
            tts g.FStar_Tactics_Types.context g.FStar_Tactics_Types.goal_ty
             in
          fail1 "goal is not irrelevant: cannot dispatch to smt (%s)"
            uu____1921))
  
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
             let uu____1962 =
               try
                 let uu____1996 =
                   let uu____2005 = FStar_BigInt.to_int_fs n1  in
                   FStar_List.splitAt uu____2005 p.FStar_Tactics_Types.goals
                    in
                 ret uu____1996
               with | uu____2027 -> fail "divide: not enough goals"  in
             bind uu____1962
               (fun uu____2054  ->
                  match uu____2054 with
                  | (lgs,rgs) ->
                      let lp =
                        let uu___78_2080 = p  in
                        {
                          FStar_Tactics_Types.main_context =
                            (uu___78_2080.FStar_Tactics_Types.main_context);
                          FStar_Tactics_Types.main_goal =
                            (uu___78_2080.FStar_Tactics_Types.main_goal);
                          FStar_Tactics_Types.all_implicits =
                            (uu___78_2080.FStar_Tactics_Types.all_implicits);
                          FStar_Tactics_Types.goals = lgs;
                          FStar_Tactics_Types.smt_goals = [];
                          FStar_Tactics_Types.depth =
                            (uu___78_2080.FStar_Tactics_Types.depth);
                          FStar_Tactics_Types.__dump =
                            (uu___78_2080.FStar_Tactics_Types.__dump);
                          FStar_Tactics_Types.psc =
                            (uu___78_2080.FStar_Tactics_Types.psc);
                          FStar_Tactics_Types.entry_range =
                            (uu___78_2080.FStar_Tactics_Types.entry_range);
                          FStar_Tactics_Types.guard_policy =
                            (uu___78_2080.FStar_Tactics_Types.guard_policy)
                        }  in
                      let rp =
                        let uu___79_2082 = p  in
                        {
                          FStar_Tactics_Types.main_context =
                            (uu___79_2082.FStar_Tactics_Types.main_context);
                          FStar_Tactics_Types.main_goal =
                            (uu___79_2082.FStar_Tactics_Types.main_goal);
                          FStar_Tactics_Types.all_implicits =
                            (uu___79_2082.FStar_Tactics_Types.all_implicits);
                          FStar_Tactics_Types.goals = rgs;
                          FStar_Tactics_Types.smt_goals = [];
                          FStar_Tactics_Types.depth =
                            (uu___79_2082.FStar_Tactics_Types.depth);
                          FStar_Tactics_Types.__dump =
                            (uu___79_2082.FStar_Tactics_Types.__dump);
                          FStar_Tactics_Types.psc =
                            (uu___79_2082.FStar_Tactics_Types.psc);
                          FStar_Tactics_Types.entry_range =
                            (uu___79_2082.FStar_Tactics_Types.entry_range);
                          FStar_Tactics_Types.guard_policy =
                            (uu___79_2082.FStar_Tactics_Types.guard_policy)
                        }  in
                      let uu____2083 = set lp  in
                      bind uu____2083
                        (fun uu____2091  ->
                           bind l
                             (fun a  ->
                                bind get
                                  (fun lp'  ->
                                     let uu____2105 = set rp  in
                                     bind uu____2105
                                       (fun uu____2113  ->
                                          bind r
                                            (fun b  ->
                                               bind get
                                                 (fun rp'  ->
                                                    let p' =
                                                      let uu___80_2129 = p
                                                         in
                                                      {
                                                        FStar_Tactics_Types.main_context
                                                          =
                                                          (uu___80_2129.FStar_Tactics_Types.main_context);
                                                        FStar_Tactics_Types.main_goal
                                                          =
                                                          (uu___80_2129.FStar_Tactics_Types.main_goal);
                                                        FStar_Tactics_Types.all_implicits
                                                          =
                                                          (uu___80_2129.FStar_Tactics_Types.all_implicits);
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
                                                          (uu___80_2129.FStar_Tactics_Types.depth);
                                                        FStar_Tactics_Types.__dump
                                                          =
                                                          (uu___80_2129.FStar_Tactics_Types.__dump);
                                                        FStar_Tactics_Types.psc
                                                          =
                                                          (uu___80_2129.FStar_Tactics_Types.psc);
                                                        FStar_Tactics_Types.entry_range
                                                          =
                                                          (uu___80_2129.FStar_Tactics_Types.entry_range);
                                                        FStar_Tactics_Types.guard_policy
                                                          =
                                                          (uu___80_2129.FStar_Tactics_Types.guard_policy)
                                                      }  in
                                                    let uu____2130 = set p'
                                                       in
                                                    bind uu____2130
                                                      (fun uu____2138  ->
                                                         ret (a, b))))))))))
  
let focus : 'a . 'a tac -> 'a tac =
  fun f  ->
    let uu____2156 = divide FStar_BigInt.one f idtac  in
    bind uu____2156
      (fun uu____2169  -> match uu____2169 with | (a,()) -> ret a)
  
let rec map : 'a . 'a tac -> 'a Prims.list tac =
  fun tau  ->
    bind get
      (fun p  ->
         match p.FStar_Tactics_Types.goals with
         | [] -> ret []
         | uu____2203::uu____2204 ->
             let uu____2207 =
               let uu____2216 = map tau  in
               divide FStar_BigInt.one tau uu____2216  in
             bind uu____2207
               (fun uu____2234  ->
                  match uu____2234 with | (h,t) -> ret (h :: t)))
  
let (seq : Prims.unit tac -> Prims.unit tac -> Prims.unit tac) =
  fun t1  ->
    fun t2  ->
      let uu____2271 =
        bind t1
          (fun uu____2276  ->
             let uu____2277 = map t2  in
             bind uu____2277 (fun uu____2285  -> ret ()))
         in
      focus uu____2271
  
let (intro : FStar_Syntax_Syntax.binder tac) =
  let uu____2292 =
    bind cur_goal
      (fun goal  ->
         let uu____2301 =
           FStar_Syntax_Util.arrow_one goal.FStar_Tactics_Types.goal_ty  in
         match uu____2301 with
         | FStar_Pervasives_Native.Some (b,c) ->
             let uu____2316 =
               let uu____2317 = FStar_Syntax_Util.is_total_comp c  in
               Prims.op_Negation uu____2317  in
             if uu____2316
             then fail "Codomain is effectful"
             else
               (let env' =
                  FStar_TypeChecker_Env.push_binders
                    goal.FStar_Tactics_Types.context [b]
                   in
                let typ' = comp_to_typ c  in
                let uu____2323 = new_uvar "intro" env' typ'  in
                bind uu____2323
                  (fun u  ->
                     let uu____2329 =
                       let uu____2332 =
                         FStar_Syntax_Util.abs [b] u
                           FStar_Pervasives_Native.None
                          in
                       trysolve goal uu____2332  in
                     bind uu____2329
                       (fun bb  ->
                          if bb
                          then
                            let uu____2338 =
                              let uu____2341 =
                                let uu___83_2342 = goal  in
                                let uu____2343 = bnorm env' u  in
                                let uu____2344 = bnorm env' typ'  in
                                {
                                  FStar_Tactics_Types.context = env';
                                  FStar_Tactics_Types.witness = uu____2343;
                                  FStar_Tactics_Types.goal_ty = uu____2344;
                                  FStar_Tactics_Types.opts =
                                    (uu___83_2342.FStar_Tactics_Types.opts);
                                  FStar_Tactics_Types.is_guard =
                                    (uu___83_2342.FStar_Tactics_Types.is_guard)
                                }  in
                              replace_cur uu____2341  in
                            bind uu____2338 (fun uu____2346  -> ret b)
                          else fail "unification failed")))
         | FStar_Pervasives_Native.None  ->
             let uu____2352 =
               tts goal.FStar_Tactics_Types.context
                 goal.FStar_Tactics_Types.goal_ty
                in
             fail1 "goal is not an arrow (%s)" uu____2352)
     in
  FStar_All.pipe_left (wrap_err "intro") uu____2292 
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
       (let uu____2383 =
          FStar_Syntax_Util.arrow_one goal.FStar_Tactics_Types.goal_ty  in
        match uu____2383 with
        | FStar_Pervasives_Native.Some (b,c) ->
            let uu____2402 =
              let uu____2403 = FStar_Syntax_Util.is_total_comp c  in
              Prims.op_Negation uu____2403  in
            if uu____2402
            then fail "Codomain is effectful"
            else
              (let bv =
                 FStar_Syntax_Syntax.gen_bv "__recf"
                   FStar_Pervasives_Native.None
                   goal.FStar_Tactics_Types.goal_ty
                  in
               let bs =
                 let uu____2419 = FStar_Syntax_Syntax.mk_binder bv  in
                 [uu____2419; b]  in
               let env' =
                 FStar_TypeChecker_Env.push_binders
                   goal.FStar_Tactics_Types.context bs
                  in
               let uu____2421 =
                 let uu____2424 = comp_to_typ c  in
                 new_uvar "intro_rec" env' uu____2424  in
               bind uu____2421
                 (fun u  ->
                    let lb =
                      let uu____2439 =
                        FStar_Syntax_Util.abs [b] u
                          FStar_Pervasives_Native.None
                         in
                      FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl bv) []
                        goal.FStar_Tactics_Types.goal_ty
                        FStar_Parser_Const.effect_Tot_lid uu____2439 []
                        FStar_Range.dummyRange
                       in
                    let body = FStar_Syntax_Syntax.bv_to_name bv  in
                    let uu____2445 =
                      FStar_Syntax_Subst.close_let_rec [lb] body  in
                    match uu____2445 with
                    | (lbs,body1) ->
                        let tm =
                          FStar_Syntax_Syntax.mk
                            (FStar_Syntax_Syntax.Tm_let ((true, lbs), body1))
                            FStar_Pervasives_Native.None
                            (goal.FStar_Tactics_Types.witness).FStar_Syntax_Syntax.pos
                           in
                        let uu____2475 = trysolve goal tm  in
                        bind uu____2475
                          (fun bb  ->
                             if bb
                             then
                               let uu____2491 =
                                 let uu____2494 =
                                   let uu___84_2495 = goal  in
                                   let uu____2496 = bnorm env' u  in
                                   let uu____2497 =
                                     let uu____2498 = comp_to_typ c  in
                                     bnorm env' uu____2498  in
                                   {
                                     FStar_Tactics_Types.context = env';
                                     FStar_Tactics_Types.witness = uu____2496;
                                     FStar_Tactics_Types.goal_ty = uu____2497;
                                     FStar_Tactics_Types.opts =
                                       (uu___84_2495.FStar_Tactics_Types.opts);
                                     FStar_Tactics_Types.is_guard =
                                       (uu___84_2495.FStar_Tactics_Types.is_guard)
                                   }  in
                                 replace_cur uu____2494  in
                               bind uu____2491
                                 (fun uu____2505  ->
                                    let uu____2506 =
                                      let uu____2511 =
                                        FStar_Syntax_Syntax.mk_binder bv  in
                                      (uu____2511, b)  in
                                    ret uu____2506)
                             else fail "intro_rec: unification failed")))
        | FStar_Pervasives_Native.None  ->
            let uu____2525 =
              tts goal.FStar_Tactics_Types.context
                goal.FStar_Tactics_Types.goal_ty
               in
            fail1 "intro_rec: goal is not an arrow (%s)" uu____2525))
  
let (norm : FStar_Syntax_Embeddings.norm_step Prims.list -> Prims.unit tac) =
  fun s  ->
    bind cur_goal
      (fun goal  ->
         mlog
           (fun uu____2545  ->
              let uu____2546 =
                FStar_Syntax_Print.term_to_string
                  goal.FStar_Tactics_Types.witness
                 in
              FStar_Util.print1 "norm: witness = %s\n" uu____2546)
           (fun uu____2551  ->
              let steps =
                let uu____2555 = FStar_TypeChecker_Normalize.tr_norm_steps s
                   in
                FStar_List.append
                  [FStar_TypeChecker_Normalize.Reify;
                  FStar_TypeChecker_Normalize.UnfoldTac] uu____2555
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
                (let uu___85_2562 = goal  in
                 {
                   FStar_Tactics_Types.context =
                     (uu___85_2562.FStar_Tactics_Types.context);
                   FStar_Tactics_Types.witness = w;
                   FStar_Tactics_Types.goal_ty = t;
                   FStar_Tactics_Types.opts =
                     (uu___85_2562.FStar_Tactics_Types.opts);
                   FStar_Tactics_Types.is_guard =
                     (uu___85_2562.FStar_Tactics_Types.is_guard)
                 })))
  
let (norm_term_env :
  env ->
    FStar_Syntax_Embeddings.norm_step Prims.list ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac)
  =
  fun e  ->
    fun s  ->
      fun t  ->
        let uu____2580 =
          mlog
            (fun uu____2585  ->
               let uu____2586 = FStar_Syntax_Print.term_to_string t  in
               FStar_Util.print1 "norm_term: tm = %s\n" uu____2586)
            (fun uu____2588  ->
               bind get
                 (fun ps  ->
                    let opts =
                      match ps.FStar_Tactics_Types.goals with
                      | g::uu____2594 -> g.FStar_Tactics_Types.opts
                      | uu____2597 -> FStar_Options.peek ()  in
                    mlog
                      (fun uu____2602  ->
                         let uu____2603 =
                           tts ps.FStar_Tactics_Types.main_context t  in
                         FStar_Util.print1 "norm_term_env: t = %s\n"
                           uu____2603)
                      (fun uu____2606  ->
                         let uu____2607 = __tc e t  in
                         bind uu____2607
                           (fun uu____2628  ->
                              match uu____2628 with
                              | (t1,uu____2638,uu____2639) ->
                                  let steps =
                                    let uu____2643 =
                                      FStar_TypeChecker_Normalize.tr_norm_steps
                                        s
                                       in
                                    FStar_List.append
                                      [FStar_TypeChecker_Normalize.Reify;
                                      FStar_TypeChecker_Normalize.UnfoldTac]
                                      uu____2643
                                     in
                                  let t2 =
                                    normalize steps
                                      ps.FStar_Tactics_Types.main_context t1
                                     in
                                  ret t2))))
           in
        FStar_All.pipe_left (wrap_err "norm_term") uu____2580
  
let (refine_intro : Prims.unit tac) =
  let uu____2655 =
    bind cur_goal
      (fun g  ->
         let uu____2662 =
           FStar_TypeChecker_Rel.base_and_refinement
             g.FStar_Tactics_Types.context g.FStar_Tactics_Types.goal_ty
            in
         match uu____2662 with
         | (uu____2675,FStar_Pervasives_Native.None ) ->
             fail "not a refinement"
         | (t,FStar_Pervasives_Native.Some (bv,phi)) ->
             let g1 =
               let uu___86_2700 = g  in
               {
                 FStar_Tactics_Types.context =
                   (uu___86_2700.FStar_Tactics_Types.context);
                 FStar_Tactics_Types.witness =
                   (uu___86_2700.FStar_Tactics_Types.witness);
                 FStar_Tactics_Types.goal_ty = t;
                 FStar_Tactics_Types.opts =
                   (uu___86_2700.FStar_Tactics_Types.opts);
                 FStar_Tactics_Types.is_guard =
                   (uu___86_2700.FStar_Tactics_Types.is_guard)
               }  in
             let uu____2701 =
               let uu____2706 =
                 let uu____2711 =
                   let uu____2712 = FStar_Syntax_Syntax.mk_binder bv  in
                   [uu____2712]  in
                 FStar_Syntax_Subst.open_term uu____2711 phi  in
               match uu____2706 with
               | (bvs,phi1) ->
                   let uu____2719 =
                     let uu____2720 = FStar_List.hd bvs  in
                     FStar_Pervasives_Native.fst uu____2720  in
                   (uu____2719, phi1)
                in
             (match uu____2701 with
              | (bv1,phi1) ->
                  let uu____2733 =
                    let uu____2736 =
                      FStar_Syntax_Subst.subst
                        [FStar_Syntax_Syntax.NT
                           (bv1, (g.FStar_Tactics_Types.witness))] phi1
                       in
                    mk_irrelevant_goal "refine_intro refinement"
                      g.FStar_Tactics_Types.context uu____2736
                      g.FStar_Tactics_Types.opts
                     in
                  bind uu____2733
                    (fun g2  ->
                       bind __dismiss (fun uu____2740  -> add_goals [g1; g2]))))
     in
  FStar_All.pipe_left (wrap_err "refine_intro") uu____2655 
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
           let uu____2761 = __tc env t  in
           bind uu____2761
             (fun uu____2781  ->
                match uu____2781 with
                | (t1,typ,guard) ->
                    let uu____2793 =
                      proc_guard "__exact typing"
                        goal.FStar_Tactics_Types.context guard
                        goal.FStar_Tactics_Types.opts
                       in
                    bind uu____2793
                      (fun uu____2797  ->
                         mlog
                           (fun uu____2801  ->
                              let uu____2802 =
                                tts goal.FStar_Tactics_Types.context typ  in
                              let uu____2803 =
                                tts goal.FStar_Tactics_Types.context
                                  goal.FStar_Tactics_Types.goal_ty
                                 in
                              FStar_Util.print2 "exact: unifying %s and %s\n"
                                uu____2802 uu____2803)
                           (fun uu____2806  ->
                              let uu____2807 =
                                do_unify goal.FStar_Tactics_Types.context typ
                                  goal.FStar_Tactics_Types.goal_ty
                                 in
                              bind uu____2807
                                (fun b  ->
                                   if b
                                   then solve goal t1
                                   else
                                     (let uu____2815 =
                                        tts goal.FStar_Tactics_Types.context
                                          t1
                                         in
                                      let uu____2816 =
                                        tts goal.FStar_Tactics_Types.context
                                          typ
                                         in
                                      let uu____2817 =
                                        tts goal.FStar_Tactics_Types.context
                                          goal.FStar_Tactics_Types.goal_ty
                                         in
                                      let uu____2818 =
                                        tts goal.FStar_Tactics_Types.context
                                          goal.FStar_Tactics_Types.witness
                                         in
                                      fail4
                                        "%s : %s does not exactly solve the goal %s (witness = %s)"
                                        uu____2815 uu____2816 uu____2817
                                        uu____2818))))))
  
let (t_exact : Prims.bool -> FStar_Syntax_Syntax.term -> Prims.unit tac) =
  fun set_expected_typ1  ->
    fun tm  ->
      let uu____2829 =
        mlog
          (fun uu____2834  ->
             let uu____2835 = FStar_Syntax_Print.term_to_string tm  in
             FStar_Util.print1 "t_exact: tm = %s\n" uu____2835)
          (fun uu____2838  ->
             let uu____2839 =
               let uu____2846 = __exact_now set_expected_typ1 tm  in
               trytac' uu____2846  in
             bind uu____2839
               (fun uu___56_2855  ->
                  match uu___56_2855 with
                  | FStar_Util.Inr r -> ret ()
                  | FStar_Util.Inl e ->
                      let uu____2864 =
                        let uu____2871 =
                          let uu____2874 =
                            norm [FStar_Syntax_Embeddings.Delta]  in
                          bind uu____2874
                            (fun uu____2878  ->
                               bind refine_intro
                                 (fun uu____2880  ->
                                    __exact_now set_expected_typ1 tm))
                           in
                        trytac' uu____2871  in
                      bind uu____2864
                        (fun uu___55_2887  ->
                           match uu___55_2887 with
                           | FStar_Util.Inr r -> ret ()
                           | FStar_Util.Inl uu____2895 -> fail e)))
         in
      FStar_All.pipe_left (wrap_err "exact") uu____2829
  
let (uvar_free_in_goal :
  FStar_Syntax_Syntax.uvar -> FStar_Tactics_Types.goal -> Prims.bool) =
  fun u  ->
    fun g  ->
      if g.FStar_Tactics_Types.is_guard
      then false
      else
        (let free_uvars =
           let uu____2910 =
             let uu____2917 =
               FStar_Syntax_Free.uvars g.FStar_Tactics_Types.goal_ty  in
             FStar_Util.set_elements uu____2917  in
           FStar_List.map FStar_Pervasives_Native.fst uu____2910  in
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
          let uu____2977 = f x  in
          bind uu____2977
            (fun y  ->
               let uu____2985 = mapM f xs  in
               bind uu____2985 (fun ys  -> ret (y :: ys)))
  
exception NoUnif 
let (uu___is_NoUnif : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with | NoUnif  -> true | uu____3003 -> false
  
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
               (fun uu____3021  ->
                  let uu____3022 = FStar_Syntax_Print.term_to_string tm  in
                  FStar_Util.print1 ">>> Calling __exact(%s)\n" uu____3022)
               (fun uu____3025  ->
                  let uu____3026 =
                    let uu____3031 =
                      let uu____3034 = t_exact false tm  in
                      with_policy FStar_Tactics_Types.Force uu____3034  in
                    trytac_exn uu____3031  in
                  bind uu____3026
                    (fun uu___57_3041  ->
                       match uu___57_3041 with
                       | FStar_Pervasives_Native.Some r -> ret ()
                       | FStar_Pervasives_Native.None  ->
                           mlog
                             (fun uu____3049  ->
                                let uu____3050 =
                                  FStar_Syntax_Print.term_to_string typ  in
                                FStar_Util.print1 ">>> typ = %s\n" uu____3050)
                             (fun uu____3053  ->
                                let uu____3054 =
                                  FStar_Syntax_Util.arrow_one typ  in
                                match uu____3054 with
                                | FStar_Pervasives_Native.None  ->
                                    FStar_Exn.raise NoUnif
                                | FStar_Pervasives_Native.Some ((bv,aq),c) ->
                                    mlog
                                      (fun uu____3086  ->
                                         let uu____3087 =
                                           FStar_Syntax_Print.binder_to_string
                                             (bv, aq)
                                            in
                                         FStar_Util.print1
                                           "__apply: pushing binder %s\n"
                                           uu____3087)
                                      (fun uu____3090  ->
                                         let uu____3091 =
                                           let uu____3092 =
                                             FStar_Syntax_Util.is_total_comp
                                               c
                                              in
                                           Prims.op_Negation uu____3092  in
                                         if uu____3091
                                         then
                                           fail "apply: not total codomain"
                                         else
                                           (let uu____3096 =
                                              new_uvar "apply"
                                                goal.FStar_Tactics_Types.context
                                                bv.FStar_Syntax_Syntax.sort
                                               in
                                            bind uu____3096
                                              (fun u  ->
                                                 let tm' =
                                                   FStar_Syntax_Syntax.mk_Tm_app
                                                     tm [(u, aq)]
                                                     FStar_Pervasives_Native.None
                                                     tm.FStar_Syntax_Syntax.pos
                                                    in
                                                 let typ' =
                                                   let uu____3116 =
                                                     comp_to_typ c  in
                                                   FStar_All.pipe_left
                                                     (FStar_Syntax_Subst.subst
                                                        [FStar_Syntax_Syntax.NT
                                                           (bv, u)])
                                                     uu____3116
                                                    in
                                                 let uu____3117 =
                                                   __apply uopt tm' typ'  in
                                                 bind uu____3117
                                                   (fun uu____3125  ->
                                                      let u1 =
                                                        bnorm
                                                          goal.FStar_Tactics_Types.context
                                                          u
                                                         in
                                                      let uu____3127 =
                                                        let uu____3128 =
                                                          let uu____3131 =
                                                            let uu____3132 =
                                                              FStar_Syntax_Util.head_and_args
                                                                u1
                                                               in
                                                            FStar_Pervasives_Native.fst
                                                              uu____3132
                                                             in
                                                          FStar_Syntax_Subst.compress
                                                            uu____3131
                                                           in
                                                        uu____3128.FStar_Syntax_Syntax.n
                                                         in
                                                      match uu____3127 with
                                                      | FStar_Syntax_Syntax.Tm_uvar
                                                          (uvar,uu____3160)
                                                          ->
                                                          bind get
                                                            (fun ps  ->
                                                               let uu____3188
                                                                 =
                                                                 uopt &&
                                                                   (uvar_free
                                                                    uvar ps)
                                                                  in
                                                               if uu____3188
                                                               then ret ()
                                                               else
                                                                 (let uu____3192
                                                                    =
                                                                    let uu____3195
                                                                    =
                                                                    let uu___87_3196
                                                                    = goal
                                                                     in
                                                                    let uu____3197
                                                                    =
                                                                    bnorm
                                                                    goal.FStar_Tactics_Types.context
                                                                    u1  in
                                                                    let uu____3198
                                                                    =
                                                                    bnorm
                                                                    goal.FStar_Tactics_Types.context
                                                                    bv.FStar_Syntax_Syntax.sort
                                                                     in
                                                                    {
                                                                    FStar_Tactics_Types.context
                                                                    =
                                                                    (uu___87_3196.FStar_Tactics_Types.context);
                                                                    FStar_Tactics_Types.witness
                                                                    =
                                                                    uu____3197;
                                                                    FStar_Tactics_Types.goal_ty
                                                                    =
                                                                    uu____3198;
                                                                    FStar_Tactics_Types.opts
                                                                    =
                                                                    (uu___87_3196.FStar_Tactics_Types.opts);
                                                                    FStar_Tactics_Types.is_guard
                                                                    = false
                                                                    }  in
                                                                    [uu____3195]
                                                                     in
                                                                  add_goals
                                                                    uu____3192))
                                                      | t -> ret ()))))))))
  
let try_unif : 'a . 'a tac -> 'a tac -> 'a tac =
  fun t  ->
    fun t'  -> mk_tac (fun ps  -> try run t ps with | NoUnif  -> run t' ps)
  
let (apply : Prims.bool -> FStar_Syntax_Syntax.term -> Prims.unit tac) =
  fun uopt  ->
    fun tm  ->
      let uu____3244 =
        mlog
          (fun uu____3249  ->
             let uu____3250 = FStar_Syntax_Print.term_to_string tm  in
             FStar_Util.print1 "apply: tm = %s\n" uu____3250)
          (fun uu____3252  ->
             bind cur_goal
               (fun goal  ->
                  let uu____3256 = __tc goal.FStar_Tactics_Types.context tm
                     in
                  bind uu____3256
                    (fun uu____3278  ->
                       match uu____3278 with
                       | (tm1,typ,guard) ->
                           let typ1 =
                             bnorm goal.FStar_Tactics_Types.context typ  in
                           let uu____3291 =
                             let uu____3294 =
                               let uu____3297 = __apply uopt tm1 typ1  in
                               bind uu____3297
                                 (fun uu____3301  ->
                                    proc_guard "apply guard"
                                      goal.FStar_Tactics_Types.context guard
                                      goal.FStar_Tactics_Types.opts)
                                in
                             focus uu____3294  in
                           let uu____3302 =
                             let uu____3305 =
                               tts goal.FStar_Tactics_Types.context tm1  in
                             let uu____3306 =
                               tts goal.FStar_Tactics_Types.context typ1  in
                             let uu____3307 =
                               tts goal.FStar_Tactics_Types.context
                                 goal.FStar_Tactics_Types.goal_ty
                                in
                             fail3
                               "Cannot instantiate %s (of type %s) to match goal (%s)"
                               uu____3305 uu____3306 uu____3307
                              in
                           try_unif uu____3291 uu____3302)))
         in
      FStar_All.pipe_left (wrap_err "apply") uu____3244
  
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
      let uu____3334 =
        match ct.FStar_Syntax_Syntax.effect_args with
        | pre::post::uu____3353 ->
            ((FStar_Pervasives_Native.fst pre),
              (FStar_Pervasives_Native.fst post))
        | uu____3394 -> failwith "apply_lemma: impossible: not a lemma"  in
      match uu____3334 with
      | (pre,post) ->
          let post1 =
            let uu____3430 =
              let uu____3439 =
                FStar_Syntax_Syntax.as_arg FStar_Syntax_Util.exp_unit  in
              [uu____3439]  in
            FStar_Syntax_Util.mk_app post uu____3430  in
          FStar_Pervasives_Native.Some (pre, post1)
    else
      if FStar_Syntax_Util.is_pure_effect ct.FStar_Syntax_Syntax.effect_name
      then
        (let uu____3459 =
           FStar_Syntax_Util.un_squash ct.FStar_Syntax_Syntax.result_typ  in
         FStar_Util.map_opt uu____3459
           (fun post  -> (FStar_Syntax_Util.t_true, post)))
      else FStar_Pervasives_Native.None
  
let (apply_lemma : FStar_Syntax_Syntax.term -> Prims.unit tac) =
  fun tm  ->
    let uu____3490 =
      let uu____3493 =
        mlog
          (fun uu____3498  ->
             let uu____3499 = FStar_Syntax_Print.term_to_string tm  in
             FStar_Util.print1 "apply_lemma: tm = %s\n" uu____3499)
          (fun uu____3502  ->
             let is_unit_t t =
               let uu____3507 =
                 let uu____3508 = FStar_Syntax_Subst.compress t  in
                 uu____3508.FStar_Syntax_Syntax.n  in
               match uu____3507 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.unit_lid
                   -> true
               | uu____3512 -> false  in
             bind cur_goal
               (fun goal  ->
                  let uu____3516 = __tc goal.FStar_Tactics_Types.context tm
                     in
                  bind uu____3516
                    (fun uu____3539  ->
                       match uu____3539 with
                       | (tm1,t,guard) ->
                           let uu____3551 =
                             FStar_Syntax_Util.arrow_formals_comp t  in
                           (match uu____3551 with
                            | (bs,comp) ->
                                let uu____3578 = lemma_or_sq comp  in
                                (match uu____3578 with
                                 | FStar_Pervasives_Native.None  ->
                                     fail "not a lemma or squashed function"
                                 | FStar_Pervasives_Native.Some (pre,post) ->
                                     let uu____3597 =
                                       FStar_List.fold_left
                                         (fun uu____3643  ->
                                            fun uu____3644  ->
                                              match (uu____3643, uu____3644)
                                              with
                                              | ((uvs,guard1,subst1),(b,aq))
                                                  ->
                                                  let b_t =
                                                    FStar_Syntax_Subst.subst
                                                      subst1
                                                      b.FStar_Syntax_Syntax.sort
                                                     in
                                                  let uu____3747 =
                                                    is_unit_t b_t  in
                                                  if uu____3747
                                                  then
                                                    (((FStar_Syntax_Util.exp_unit,
                                                        aq) :: uvs), guard1,
                                                      ((FStar_Syntax_Syntax.NT
                                                          (b,
                                                            FStar_Syntax_Util.exp_unit))
                                                      :: subst1))
                                                  else
                                                    (let uu____3785 =
                                                       FStar_TypeChecker_Util.new_implicit_var
                                                         "apply_lemma"
                                                         (goal.FStar_Tactics_Types.goal_ty).FStar_Syntax_Syntax.pos
                                                         goal.FStar_Tactics_Types.context
                                                         b_t
                                                        in
                                                     match uu____3785 with
                                                     | (u,uu____3815,g_u) ->
                                                         let uu____3829 =
                                                           FStar_TypeChecker_Rel.conj_guard
                                                             guard1 g_u
                                                            in
                                                         (((u, aq) :: uvs),
                                                           uu____3829,
                                                           ((FStar_Syntax_Syntax.NT
                                                               (b, u)) ::
                                                           subst1))))
                                         ([], guard, []) bs
                                        in
                                     (match uu____3597 with
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
                                          let uu____3900 =
                                            let uu____3903 =
                                              FStar_Syntax_Util.mk_squash
                                                FStar_Syntax_Syntax.U_zero
                                                post1
                                               in
                                            do_unify
                                              goal.FStar_Tactics_Types.context
                                              uu____3903
                                              goal.FStar_Tactics_Types.goal_ty
                                             in
                                          bind uu____3900
                                            (fun b  ->
                                               if Prims.op_Negation b
                                               then
                                                 let uu____3911 =
                                                   tts
                                                     goal.FStar_Tactics_Types.context
                                                     tm1
                                                    in
                                                 let uu____3912 =
                                                   let uu____3913 =
                                                     FStar_Syntax_Util.mk_squash
                                                       FStar_Syntax_Syntax.U_zero
                                                       post1
                                                      in
                                                   tts
                                                     goal.FStar_Tactics_Types.context
                                                     uu____3913
                                                    in
                                                 let uu____3914 =
                                                   tts
                                                     goal.FStar_Tactics_Types.context
                                                     goal.FStar_Tactics_Types.goal_ty
                                                    in
                                                 fail3
                                                   "Cannot instantiate lemma %s (with postcondition: %s) to match goal (%s)"
                                                   uu____3911 uu____3912
                                                   uu____3914
                                               else
                                                 (let uu____3916 =
                                                    add_implicits
                                                      implicits.FStar_TypeChecker_Env.implicits
                                                     in
                                                  bind uu____3916
                                                    (fun uu____3921  ->
                                                       let uu____3922 =
                                                         solve goal
                                                           FStar_Syntax_Util.exp_unit
                                                          in
                                                       bind uu____3922
                                                         (fun uu____3930  ->
                                                            let is_free_uvar
                                                              uv t1 =
                                                              let free_uvars
                                                                =
                                                                let uu____3941
                                                                  =
                                                                  let uu____3948
                                                                    =
                                                                    FStar_Syntax_Free.uvars
                                                                    t1  in
                                                                  FStar_Util.set_elements
                                                                    uu____3948
                                                                   in
                                                                FStar_List.map
                                                                  FStar_Pervasives_Native.fst
                                                                  uu____3941
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
                                                              let uu____3989
                                                                =
                                                                FStar_Syntax_Util.head_and_args
                                                                  t1
                                                                 in
                                                              match uu____3989
                                                              with
                                                              | (hd1,uu____4005)
                                                                  ->
                                                                  (match 
                                                                    hd1.FStar_Syntax_Syntax.n
                                                                   with
                                                                   | 
                                                                   FStar_Syntax_Syntax.Tm_uvar
                                                                    (uv,uu____4027)
                                                                    ->
                                                                    appears
                                                                    uv goals
                                                                   | 
                                                                   uu____4052
                                                                    -> false)
                                                               in
                                                            let uu____4053 =
                                                              FStar_All.pipe_right
                                                                implicits.FStar_TypeChecker_Env.implicits
                                                                (mapM
                                                                   (fun
                                                                    uu____4125
                                                                     ->
                                                                    match uu____4125
                                                                    with
                                                                    | 
                                                                    (_msg,env,_uvar,term,typ,uu____4153)
                                                                    ->
                                                                    let uu____4154
                                                                    =
                                                                    FStar_Syntax_Util.head_and_args
                                                                    term  in
                                                                    (match uu____4154
                                                                    with
                                                                    | 
                                                                    (hd1,uu____4180)
                                                                    ->
                                                                    let uu____4201
                                                                    =
                                                                    let uu____4202
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    hd1  in
                                                                    uu____4202.FStar_Syntax_Syntax.n
                                                                     in
                                                                    (match uu____4201
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Tm_uvar
                                                                    uu____4215
                                                                    ->
                                                                    let uu____4232
                                                                    =
                                                                    let uu____4241
                                                                    =
                                                                    let uu____4244
                                                                    =
                                                                    let uu___90_4245
                                                                    = goal
                                                                     in
                                                                    let uu____4246
                                                                    =
                                                                    bnorm
                                                                    goal.FStar_Tactics_Types.context
                                                                    term  in
                                                                    let uu____4247
                                                                    =
                                                                    bnorm
                                                                    goal.FStar_Tactics_Types.context
                                                                    typ  in
                                                                    {
                                                                    FStar_Tactics_Types.context
                                                                    =
                                                                    (uu___90_4245.FStar_Tactics_Types.context);
                                                                    FStar_Tactics_Types.witness
                                                                    =
                                                                    uu____4246;
                                                                    FStar_Tactics_Types.goal_ty
                                                                    =
                                                                    uu____4247;
                                                                    FStar_Tactics_Types.opts
                                                                    =
                                                                    (uu___90_4245.FStar_Tactics_Types.opts);
                                                                    FStar_Tactics_Types.is_guard
                                                                    =
                                                                    (uu___90_4245.FStar_Tactics_Types.is_guard)
                                                                    }  in
                                                                    [uu____4244]
                                                                     in
                                                                    (uu____4241,
                                                                    [])  in
                                                                    ret
                                                                    uu____4232
                                                                    | 
                                                                    uu____4260
                                                                    ->
                                                                    let g_typ
                                                                    =
                                                                    let uu____4262
                                                                    =
                                                                    FStar_Options.__temp_fast_implicits
                                                                    ()  in
                                                                    if
                                                                    uu____4262
                                                                    then
                                                                    FStar_TypeChecker_TcTerm.check_type_of_well_typed_term
                                                                    false env
                                                                    term typ
                                                                    else
                                                                    (let term1
                                                                    =
                                                                    bnorm env
                                                                    term  in
                                                                    let uu____4265
                                                                    =
                                                                    let uu____4272
                                                                    =
                                                                    FStar_TypeChecker_Env.set_expected_typ
                                                                    env typ
                                                                     in
                                                                    env.FStar_TypeChecker_Env.type_of
                                                                    uu____4272
                                                                    term1  in
                                                                    match uu____4265
                                                                    with
                                                                    | 
                                                                    (uu____4273,uu____4274,g_typ)
                                                                    -> g_typ)
                                                                     in
                                                                    let uu____4276
                                                                    =
                                                                    goal_from_guard
                                                                    "apply_lemma solved arg"
                                                                    goal.FStar_Tactics_Types.context
                                                                    g_typ
                                                                    goal.FStar_Tactics_Types.opts
                                                                     in
                                                                    bind
                                                                    uu____4276
                                                                    (fun
                                                                    uu___58_4292
                                                                     ->
                                                                    match uu___58_4292
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
                                                            bind uu____4053
                                                              (fun goals_  ->
                                                                 let sub_goals
                                                                   =
                                                                   let uu____4360
                                                                    =
                                                                    FStar_List.map
                                                                    FStar_Pervasives_Native.fst
                                                                    goals_
                                                                     in
                                                                   FStar_List.flatten
                                                                    uu____4360
                                                                    in
                                                                 let smt_goals
                                                                   =
                                                                   let uu____4382
                                                                    =
                                                                    FStar_List.map
                                                                    FStar_Pervasives_Native.snd
                                                                    goals_
                                                                     in
                                                                   FStar_List.flatten
                                                                    uu____4382
                                                                    in
                                                                 let rec filter'
                                                                   a f xs =
                                                                   match xs
                                                                   with
                                                                   | 
                                                                   [] -> []
                                                                   | 
                                                                   x::xs1 ->
                                                                    let uu____4437
                                                                    = f x xs1
                                                                     in
                                                                    if
                                                                    uu____4437
                                                                    then
                                                                    let uu____4440
                                                                    =
                                                                    filter'
                                                                    () f xs1
                                                                     in x ::
                                                                    uu____4440
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
                                                                    let uu____4454
                                                                    =
                                                                    checkone
                                                                    g.FStar_Tactics_Types.witness
                                                                    goals  in
                                                                    Prims.op_Negation
                                                                    uu____4454))
                                                                    a438 a439)
                                                                    (Obj.magic
                                                                    sub_goals))
                                                                    in
                                                                 let uu____4455
                                                                   =
                                                                   proc_guard
                                                                    "apply_lemma guard"
                                                                    goal.FStar_Tactics_Types.context
                                                                    guard
                                                                    goal.FStar_Tactics_Types.opts
                                                                    in
                                                                 bind
                                                                   uu____4455
                                                                   (fun
                                                                    uu____4460
                                                                     ->
                                                                    let uu____4461
                                                                    =
                                                                    let uu____4464
                                                                    =
                                                                    let uu____4465
                                                                    =
                                                                    let uu____4466
                                                                    =
                                                                    FStar_Syntax_Util.mk_squash
                                                                    FStar_Syntax_Syntax.U_zero
                                                                    pre1  in
                                                                    istrivial
                                                                    goal.FStar_Tactics_Types.context
                                                                    uu____4466
                                                                     in
                                                                    Prims.op_Negation
                                                                    uu____4465
                                                                     in
                                                                    if
                                                                    uu____4464
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
                                                                    uu____4461
                                                                    (fun
                                                                    uu____4472
                                                                     ->
                                                                    let uu____4473
                                                                    =
                                                                    add_smt_goals
                                                                    smt_goals
                                                                     in
                                                                    bind
                                                                    uu____4473
                                                                    (fun
                                                                    uu____4477
                                                                     ->
                                                                    add_goals
                                                                    sub_goals1))))))))))))))
         in
      focus uu____3493  in
    FStar_All.pipe_left (wrap_err "apply_lemma") uu____3490
  
let (destruct_eq' :
  FStar_Syntax_Syntax.typ ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun typ  ->
    let uu____4497 = FStar_Syntax_Util.destruct_typ_as_formula typ  in
    match uu____4497 with
    | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn
        (l,uu____4507::(e1,uu____4509)::(e2,uu____4511)::[])) when
        FStar_Ident.lid_equals l FStar_Parser_Const.eq2_lid ->
        FStar_Pervasives_Native.Some (e1, e2)
    | uu____4570 -> FStar_Pervasives_Native.None
  
let (destruct_eq :
  FStar_Syntax_Syntax.typ ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun typ  ->
    let uu____4592 = destruct_eq' typ  in
    match uu____4592 with
    | FStar_Pervasives_Native.Some t -> FStar_Pervasives_Native.Some t
    | FStar_Pervasives_Native.None  ->
        let uu____4622 = FStar_Syntax_Util.un_squash typ  in
        (match uu____4622 with
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
        let uu____4678 = FStar_TypeChecker_Env.pop_bv e1  in
        match uu____4678 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (bv',e') ->
            if FStar_Syntax_Syntax.bv_eq bvar bv'
            then FStar_Pervasives_Native.Some (e', [])
            else
              (let uu____4726 = aux e'  in
               FStar_Util.map_opt uu____4726
                 (fun uu____4750  ->
                    match uu____4750 with | (e'',bvs) -> (e'', (bv' :: bvs))))
         in
      let uu____4771 = aux e  in
      FStar_Util.map_opt uu____4771
        (fun uu____4795  ->
           match uu____4795 with | (e',bvs) -> (e', (FStar_List.rev bvs)))
  
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
          let uu____4850 = split_env b1 g.FStar_Tactics_Types.context  in
          FStar_Util.map_opt uu____4850
            (fun uu____4874  ->
               match uu____4874 with
               | (e0,bvs) ->
                   let s1 bv =
                     let uu___91_4891 = bv  in
                     let uu____4892 =
                       FStar_Syntax_Subst.subst s bv.FStar_Syntax_Syntax.sort
                        in
                     {
                       FStar_Syntax_Syntax.ppname =
                         (uu___91_4891.FStar_Syntax_Syntax.ppname);
                       FStar_Syntax_Syntax.index =
                         (uu___91_4891.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort = uu____4892
                     }  in
                   let bvs1 = FStar_List.map s1 bvs  in
                   let c = push_bvs e0 (b2 :: bvs1)  in
                   let w =
                     FStar_Syntax_Subst.subst s g.FStar_Tactics_Types.witness
                      in
                   let t =
                     FStar_Syntax_Subst.subst s g.FStar_Tactics_Types.goal_ty
                      in
                   let uu___92_4901 = g  in
                   {
                     FStar_Tactics_Types.context = c;
                     FStar_Tactics_Types.witness = w;
                     FStar_Tactics_Types.goal_ty = t;
                     FStar_Tactics_Types.opts =
                       (uu___92_4901.FStar_Tactics_Types.opts);
                     FStar_Tactics_Types.is_guard =
                       (uu___92_4901.FStar_Tactics_Types.is_guard)
                   })
  
let (rewrite : FStar_Syntax_Syntax.binder -> Prims.unit tac) =
  fun h  ->
    bind cur_goal
      (fun goal  ->
         let uu____4914 = h  in
         match uu____4914 with
         | (bv,uu____4918) ->
             mlog
               (fun uu____4922  ->
                  let uu____4923 = FStar_Syntax_Print.bv_to_string bv  in
                  let uu____4924 =
                    tts goal.FStar_Tactics_Types.context
                      bv.FStar_Syntax_Syntax.sort
                     in
                  FStar_Util.print2 "+++Rewrite %s : %s\n" uu____4923
                    uu____4924)
               (fun uu____4927  ->
                  let uu____4928 =
                    split_env bv goal.FStar_Tactics_Types.context  in
                  match uu____4928 with
                  | FStar_Pervasives_Native.None  ->
                      fail "rewrite: binder not found in environment"
                  | FStar_Pervasives_Native.Some (e0,bvs) ->
                      let uu____4957 =
                        destruct_eq bv.FStar_Syntax_Syntax.sort  in
                      (match uu____4957 with
                       | FStar_Pervasives_Native.Some (x,e) ->
                           let uu____4972 =
                             let uu____4973 = FStar_Syntax_Subst.compress x
                                in
                             uu____4973.FStar_Syntax_Syntax.n  in
                           (match uu____4972 with
                            | FStar_Syntax_Syntax.Tm_name x1 ->
                                let s = [FStar_Syntax_Syntax.NT (x1, e)]  in
                                let s1 bv1 =
                                  let uu___93_4986 = bv1  in
                                  let uu____4987 =
                                    FStar_Syntax_Subst.subst s
                                      bv1.FStar_Syntax_Syntax.sort
                                     in
                                  {
                                    FStar_Syntax_Syntax.ppname =
                                      (uu___93_4986.FStar_Syntax_Syntax.ppname);
                                    FStar_Syntax_Syntax.index =
                                      (uu___93_4986.FStar_Syntax_Syntax.index);
                                    FStar_Syntax_Syntax.sort = uu____4987
                                  }  in
                                let bvs1 = FStar_List.map s1 bvs  in
                                let uu____4993 =
                                  let uu___94_4994 = goal  in
                                  let uu____4995 = push_bvs e0 (bv :: bvs1)
                                     in
                                  let uu____4996 =
                                    FStar_Syntax_Subst.subst s
                                      goal.FStar_Tactics_Types.witness
                                     in
                                  let uu____4997 =
                                    FStar_Syntax_Subst.subst s
                                      goal.FStar_Tactics_Types.goal_ty
                                     in
                                  {
                                    FStar_Tactics_Types.context = uu____4995;
                                    FStar_Tactics_Types.witness = uu____4996;
                                    FStar_Tactics_Types.goal_ty = uu____4997;
                                    FStar_Tactics_Types.opts =
                                      (uu___94_4994.FStar_Tactics_Types.opts);
                                    FStar_Tactics_Types.is_guard =
                                      (uu___94_4994.FStar_Tactics_Types.is_guard)
                                  }  in
                                replace_cur uu____4993
                            | uu____4998 ->
                                fail
                                  "rewrite: Not an equality hypothesis with a variable on the LHS")
                       | uu____4999 ->
                           fail "rewrite: Not an equality hypothesis")))
  
let (rename_to :
  FStar_Syntax_Syntax.binder -> Prims.string -> Prims.unit tac) =
  fun b  ->
    fun s  ->
      bind cur_goal
        (fun goal  ->
           let uu____5024 = b  in
           match uu____5024 with
           | (bv,uu____5028) ->
               let bv' =
                 FStar_Syntax_Syntax.freshen_bv
                   (let uu___95_5032 = bv  in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (FStar_Ident.mk_ident
                           (s,
                             ((bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange)));
                      FStar_Syntax_Syntax.index =
                        (uu___95_5032.FStar_Syntax_Syntax.index);
                      FStar_Syntax_Syntax.sort =
                        (uu___95_5032.FStar_Syntax_Syntax.sort)
                    })
                  in
               let s1 =
                 let uu____5036 =
                   let uu____5037 =
                     let uu____5044 = FStar_Syntax_Syntax.bv_to_name bv'  in
                     (bv, uu____5044)  in
                   FStar_Syntax_Syntax.NT uu____5037  in
                 [uu____5036]  in
               let uu____5045 = subst_goal bv bv' s1 goal  in
               (match uu____5045 with
                | FStar_Pervasives_Native.None  ->
                    fail "rename_to: binder not found in environment"
                | FStar_Pervasives_Native.Some goal1 -> replace_cur goal1))
  
let (binder_retype : FStar_Syntax_Syntax.binder -> Prims.unit tac) =
  fun b  ->
    bind cur_goal
      (fun goal  ->
         let uu____5064 = b  in
         match uu____5064 with
         | (bv,uu____5068) ->
             let uu____5069 = split_env bv goal.FStar_Tactics_Types.context
                in
             (match uu____5069 with
              | FStar_Pervasives_Native.None  ->
                  fail "binder_retype: binder is not present in environment"
              | FStar_Pervasives_Native.Some (e0,bvs) ->
                  let uu____5098 = FStar_Syntax_Util.type_u ()  in
                  (match uu____5098 with
                   | (ty,u) ->
                       let uu____5107 = new_uvar "binder_retype" e0 ty  in
                       bind uu____5107
                         (fun t'  ->
                            let bv'' =
                              let uu___96_5117 = bv  in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___96_5117.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___96_5117.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = t'
                              }  in
                            let s =
                              let uu____5121 =
                                let uu____5122 =
                                  let uu____5129 =
                                    FStar_Syntax_Syntax.bv_to_name bv''  in
                                  (bv, uu____5129)  in
                                FStar_Syntax_Syntax.NT uu____5122  in
                              [uu____5121]  in
                            let bvs1 =
                              FStar_List.map
                                (fun b1  ->
                                   let uu___97_5137 = b1  in
                                   let uu____5138 =
                                     FStar_Syntax_Subst.subst s
                                       b1.FStar_Syntax_Syntax.sort
                                      in
                                   {
                                     FStar_Syntax_Syntax.ppname =
                                       (uu___97_5137.FStar_Syntax_Syntax.ppname);
                                     FStar_Syntax_Syntax.index =
                                       (uu___97_5137.FStar_Syntax_Syntax.index);
                                     FStar_Syntax_Syntax.sort = uu____5138
                                   }) bvs
                               in
                            let env' = push_bvs e0 (bv'' :: bvs1)  in
                            bind __dismiss
                              (fun uu____5144  ->
                                 let uu____5145 =
                                   let uu____5148 =
                                     let uu____5151 =
                                       let uu___98_5152 = goal  in
                                       let uu____5153 =
                                         FStar_Syntax_Subst.subst s
                                           goal.FStar_Tactics_Types.witness
                                          in
                                       let uu____5154 =
                                         FStar_Syntax_Subst.subst s
                                           goal.FStar_Tactics_Types.goal_ty
                                          in
                                       {
                                         FStar_Tactics_Types.context = env';
                                         FStar_Tactics_Types.witness =
                                           uu____5153;
                                         FStar_Tactics_Types.goal_ty =
                                           uu____5154;
                                         FStar_Tactics_Types.opts =
                                           (uu___98_5152.FStar_Tactics_Types.opts);
                                         FStar_Tactics_Types.is_guard =
                                           (uu___98_5152.FStar_Tactics_Types.is_guard)
                                       }  in
                                     [uu____5151]  in
                                   add_goals uu____5148  in
                                 bind uu____5145
                                   (fun uu____5157  ->
                                      let uu____5158 =
                                        FStar_Syntax_Util.mk_eq2
                                          (FStar_Syntax_Syntax.U_succ u) ty
                                          bv.FStar_Syntax_Syntax.sort t'
                                         in
                                      add_irrelevant_goal
                                        "binder_retype equation" e0
                                        uu____5158
                                        goal.FStar_Tactics_Types.opts))))))
  
let (norm_binder_type :
  FStar_Syntax_Embeddings.norm_step Prims.list ->
    FStar_Syntax_Syntax.binder -> Prims.unit tac)
  =
  fun s  ->
    fun b  ->
      bind cur_goal
        (fun goal  ->
           let uu____5179 = b  in
           match uu____5179 with
           | (bv,uu____5183) ->
               let uu____5184 = split_env bv goal.FStar_Tactics_Types.context
                  in
               (match uu____5184 with
                | FStar_Pervasives_Native.None  ->
                    fail
                      "binder_retype: binder is not present in environment"
                | FStar_Pervasives_Native.Some (e0,bvs) ->
                    let steps =
                      let uu____5216 =
                        FStar_TypeChecker_Normalize.tr_norm_steps s  in
                      FStar_List.append
                        [FStar_TypeChecker_Normalize.Reify;
                        FStar_TypeChecker_Normalize.UnfoldTac] uu____5216
                       in
                    let sort' =
                      normalize steps e0 bv.FStar_Syntax_Syntax.sort  in
                    let bv' =
                      let uu___99_5221 = bv  in
                      {
                        FStar_Syntax_Syntax.ppname =
                          (uu___99_5221.FStar_Syntax_Syntax.ppname);
                        FStar_Syntax_Syntax.index =
                          (uu___99_5221.FStar_Syntax_Syntax.index);
                        FStar_Syntax_Syntax.sort = sort'
                      }  in
                    let env' = push_bvs e0 (bv' :: bvs)  in
                    replace_cur
                      (let uu___100_5225 = goal  in
                       {
                         FStar_Tactics_Types.context = env';
                         FStar_Tactics_Types.witness =
                           (uu___100_5225.FStar_Tactics_Types.witness);
                         FStar_Tactics_Types.goal_ty =
                           (uu___100_5225.FStar_Tactics_Types.goal_ty);
                         FStar_Tactics_Types.opts =
                           (uu___100_5225.FStar_Tactics_Types.opts);
                         FStar_Tactics_Types.is_guard =
                           (uu___100_5225.FStar_Tactics_Types.is_guard)
                       })))
  
let (revert : Prims.unit tac) =
  bind cur_goal
    (fun goal  ->
       let uu____5233 =
         FStar_TypeChecker_Env.pop_bv goal.FStar_Tactics_Types.context  in
       match uu____5233 with
       | FStar_Pervasives_Native.None  -> fail "Cannot revert; empty context"
       | FStar_Pervasives_Native.Some (x,env') ->
           let typ' =
             let uu____5255 =
               FStar_Syntax_Syntax.mk_Total goal.FStar_Tactics_Types.goal_ty
                in
             FStar_Syntax_Util.arrow [(x, FStar_Pervasives_Native.None)]
               uu____5255
              in
           let w' =
             FStar_Syntax_Util.abs [(x, FStar_Pervasives_Native.None)]
               goal.FStar_Tactics_Types.witness FStar_Pervasives_Native.None
              in
           replace_cur
             (let uu___101_5289 = goal  in
              {
                FStar_Tactics_Types.context = env';
                FStar_Tactics_Types.witness = w';
                FStar_Tactics_Types.goal_ty = typ';
                FStar_Tactics_Types.opts =
                  (uu___101_5289.FStar_Tactics_Types.opts);
                FStar_Tactics_Types.is_guard =
                  (uu___101_5289.FStar_Tactics_Types.is_guard)
              }))
  
let (free_in :
  FStar_Syntax_Syntax.bv -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun bv  ->
    fun t  ->
      let uu____5296 = FStar_Syntax_Free.names t  in
      FStar_Util.set_mem bv uu____5296
  
let rec (clear : FStar_Syntax_Syntax.binder -> Prims.unit tac) =
  fun b  ->
    let bv = FStar_Pervasives_Native.fst b  in
    bind cur_goal
      (fun goal  ->
         mlog
           (fun uu____5312  ->
              let uu____5313 = FStar_Syntax_Print.binder_to_string b  in
              let uu____5314 =
                let uu____5315 =
                  let uu____5316 =
                    FStar_TypeChecker_Env.all_binders
                      goal.FStar_Tactics_Types.context
                     in
                  FStar_All.pipe_right uu____5316 FStar_List.length  in
                FStar_All.pipe_right uu____5315 FStar_Util.string_of_int  in
              FStar_Util.print2 "Clear of (%s), env has %s binders\n"
                uu____5313 uu____5314)
           (fun uu____5327  ->
              let uu____5328 = split_env bv goal.FStar_Tactics_Types.context
                 in
              match uu____5328 with
              | FStar_Pervasives_Native.None  ->
                  fail "Cannot clear; binder not in environment"
              | FStar_Pervasives_Native.Some (e',bvs) ->
                  let rec check1 bvs1 =
                    match bvs1 with
                    | [] -> ret ()
                    | bv'::bvs2 ->
                        let uu____5373 =
                          free_in bv bv'.FStar_Syntax_Syntax.sort  in
                        if uu____5373
                        then
                          let uu____5376 =
                            let uu____5377 =
                              FStar_Syntax_Print.bv_to_string bv'  in
                            FStar_Util.format1
                              "Cannot clear; binder present in the type of %s"
                              uu____5377
                             in
                          fail uu____5376
                        else check1 bvs2
                     in
                  let uu____5379 =
                    free_in bv goal.FStar_Tactics_Types.goal_ty  in
                  if uu____5379
                  then fail "Cannot clear; binder present in goal"
                  else
                    (let uu____5383 = check1 bvs  in
                     bind uu____5383
                       (fun uu____5389  ->
                          let env' = push_bvs e' bvs  in
                          let uu____5391 =
                            new_uvar "clear.witness" env'
                              goal.FStar_Tactics_Types.goal_ty
                             in
                          bind uu____5391
                            (fun ut  ->
                               let uu____5397 =
                                 do_unify goal.FStar_Tactics_Types.context
                                   goal.FStar_Tactics_Types.witness ut
                                  in
                               bind uu____5397
                                 (fun b1  ->
                                    if b1
                                    then
                                      replace_cur
                                        (let uu___102_5406 = goal  in
                                         {
                                           FStar_Tactics_Types.context = env';
                                           FStar_Tactics_Types.witness = ut;
                                           FStar_Tactics_Types.goal_ty =
                                             (uu___102_5406.FStar_Tactics_Types.goal_ty);
                                           FStar_Tactics_Types.opts =
                                             (uu___102_5406.FStar_Tactics_Types.opts);
                                           FStar_Tactics_Types.is_guard =
                                             (uu___102_5406.FStar_Tactics_Types.is_guard)
                                         })
                                    else
                                      fail
                                        "Cannot clear; binder appears in witness"))))))
  
let (clear_top : Prims.unit tac) =
  bind cur_goal
    (fun goal  ->
       let uu____5415 =
         FStar_TypeChecker_Env.pop_bv goal.FStar_Tactics_Types.context  in
       match uu____5415 with
       | FStar_Pervasives_Native.None  -> fail "Cannot clear; empty context"
       | FStar_Pervasives_Native.Some (x,uu____5429) ->
           let uu____5434 = FStar_Syntax_Syntax.mk_binder x  in
           clear uu____5434)
  
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
           let uu___103_5450 = g  in
           {
             FStar_Tactics_Types.context = ctx';
             FStar_Tactics_Types.witness =
               (uu___103_5450.FStar_Tactics_Types.witness);
             FStar_Tactics_Types.goal_ty =
               (uu___103_5450.FStar_Tactics_Types.goal_ty);
             FStar_Tactics_Types.opts =
               (uu___103_5450.FStar_Tactics_Types.opts);
             FStar_Tactics_Types.is_guard =
               (uu___103_5450.FStar_Tactics_Types.is_guard)
           }  in
         bind __dismiss (fun uu____5452  -> add_goals [g']))
  
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
           let uu___104_5468 = g  in
           {
             FStar_Tactics_Types.context = ctx';
             FStar_Tactics_Types.witness =
               (uu___104_5468.FStar_Tactics_Types.witness);
             FStar_Tactics_Types.goal_ty =
               (uu___104_5468.FStar_Tactics_Types.goal_ty);
             FStar_Tactics_Types.opts =
               (uu___104_5468.FStar_Tactics_Types.opts);
             FStar_Tactics_Types.is_guard =
               (uu___104_5468.FStar_Tactics_Types.is_guard)
           }  in
         bind __dismiss (fun uu____5470  -> add_goals [g']))
  
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
            let uu____5502 = FStar_Syntax_Subst.compress t  in
            uu____5502.FStar_Syntax_Syntax.n  in
          let uu____5505 =
            if d = FStar_Tactics_Types.TopDown
            then
              f env
                (let uu___108_5511 = t  in
                 {
                   FStar_Syntax_Syntax.n = tn;
                   FStar_Syntax_Syntax.pos =
                     (uu___108_5511.FStar_Syntax_Syntax.pos);
                   FStar_Syntax_Syntax.vars =
                     (uu___108_5511.FStar_Syntax_Syntax.vars)
                 })
            else ret t  in
          bind uu____5505
            (fun t1  ->
               let ff = tac_fold_env d f env  in
               let tn1 =
                 let uu____5525 =
                   let uu____5526 = FStar_Syntax_Subst.compress t1  in
                   uu____5526.FStar_Syntax_Syntax.n  in
                 match uu____5525 with
                 | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
                     let uu____5553 = ff hd1  in
                     bind uu____5553
                       (fun hd2  ->
                          let fa uu____5573 =
                            match uu____5573 with
                            | (a,q) ->
                                let uu____5586 = ff a  in
                                bind uu____5586 (fun a1  -> ret (a1, q))
                             in
                          let uu____5599 = mapM fa args  in
                          bind uu____5599
                            (fun args1  ->
                               ret (FStar_Syntax_Syntax.Tm_app (hd2, args1))))
                 | FStar_Syntax_Syntax.Tm_abs (bs,t2,k) ->
                     let uu____5659 = FStar_Syntax_Subst.open_term bs t2  in
                     (match uu____5659 with
                      | (bs1,t') ->
                          let uu____5668 =
                            let uu____5671 =
                              FStar_TypeChecker_Env.push_binders env bs1  in
                            tac_fold_env d f uu____5671 t'  in
                          bind uu____5668
                            (fun t''  ->
                               let uu____5675 =
                                 let uu____5676 =
                                   let uu____5693 =
                                     FStar_Syntax_Subst.close_binders bs1  in
                                   let uu____5694 =
                                     FStar_Syntax_Subst.close bs1 t''  in
                                   (uu____5693, uu____5694, k)  in
                                 FStar_Syntax_Syntax.Tm_abs uu____5676  in
                               ret uu____5675))
                 | FStar_Syntax_Syntax.Tm_arrow (bs,k) -> ret tn
                 | FStar_Syntax_Syntax.Tm_match (hd1,brs) ->
                     let uu____5753 = ff hd1  in
                     bind uu____5753
                       (fun hd2  ->
                          let ffb br =
                            let uu____5766 =
                              FStar_Syntax_Subst.open_branch br  in
                            match uu____5766 with
                            | (pat,w,e) ->
                                let uu____5788 = ff e  in
                                bind uu____5788
                                  (fun e1  ->
                                     let br1 =
                                       FStar_Syntax_Subst.close_branch
                                         (pat, w, e1)
                                        in
                                     ret br1)
                             in
                          let uu____5801 = mapM ffb brs  in
                          bind uu____5801
                            (fun brs1  ->
                               ret (FStar_Syntax_Syntax.Tm_match (hd2, brs1))))
                 | FStar_Syntax_Syntax.Tm_let
                     ((false
                       ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl bv;
                          FStar_Syntax_Syntax.lbunivs = uu____5815;
                          FStar_Syntax_Syntax.lbtyp = uu____5816;
                          FStar_Syntax_Syntax.lbeff = uu____5817;
                          FStar_Syntax_Syntax.lbdef = def;
                          FStar_Syntax_Syntax.lbattrs = uu____5819;
                          FStar_Syntax_Syntax.lbpos = uu____5820;_}::[]),e)
                     ->
                     let lb =
                       let uu____5845 =
                         let uu____5846 = FStar_Syntax_Subst.compress t1  in
                         uu____5846.FStar_Syntax_Syntax.n  in
                       match uu____5845 with
                       | FStar_Syntax_Syntax.Tm_let
                           ((false ,lb::[]),uu____5850) -> lb
                       | uu____5863 -> failwith "impossible"  in
                     let fflb lb1 =
                       let uu____5870 = ff lb1.FStar_Syntax_Syntax.lbdef  in
                       bind uu____5870
                         (fun def1  ->
                            ret
                              (let uu___105_5876 = lb1  in
                               {
                                 FStar_Syntax_Syntax.lbname =
                                   (uu___105_5876.FStar_Syntax_Syntax.lbname);
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___105_5876.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp =
                                   (uu___105_5876.FStar_Syntax_Syntax.lbtyp);
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___105_5876.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def1;
                                 FStar_Syntax_Syntax.lbattrs =
                                   (uu___105_5876.FStar_Syntax_Syntax.lbattrs);
                                 FStar_Syntax_Syntax.lbpos =
                                   (uu___105_5876.FStar_Syntax_Syntax.lbpos)
                               }))
                        in
                     let uu____5877 = fflb lb  in
                     bind uu____5877
                       (fun lb1  ->
                          let uu____5886 =
                            let uu____5891 =
                              let uu____5892 =
                                FStar_Syntax_Syntax.mk_binder bv  in
                              [uu____5892]  in
                            FStar_Syntax_Subst.open_term uu____5891 e  in
                          match uu____5886 with
                          | (bs,e1) ->
                              let uu____5897 = ff e1  in
                              bind uu____5897
                                (fun e2  ->
                                   let e3 = FStar_Syntax_Subst.close bs e2
                                      in
                                   ret
                                     (FStar_Syntax_Syntax.Tm_let
                                        ((false, [lb1]), e3))))
                 | FStar_Syntax_Syntax.Tm_let ((true ,lbs),e) ->
                     let fflb lb =
                       let uu____5934 = ff lb.FStar_Syntax_Syntax.lbdef  in
                       bind uu____5934
                         (fun def  ->
                            ret
                              (let uu___106_5940 = lb  in
                               {
                                 FStar_Syntax_Syntax.lbname =
                                   (uu___106_5940.FStar_Syntax_Syntax.lbname);
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___106_5940.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp =
                                   (uu___106_5940.FStar_Syntax_Syntax.lbtyp);
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___106_5940.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def;
                                 FStar_Syntax_Syntax.lbattrs =
                                   (uu___106_5940.FStar_Syntax_Syntax.lbattrs);
                                 FStar_Syntax_Syntax.lbpos =
                                   (uu___106_5940.FStar_Syntax_Syntax.lbpos)
                               }))
                        in
                     let uu____5941 = FStar_Syntax_Subst.open_let_rec lbs e
                        in
                     (match uu____5941 with
                      | (lbs1,e1) ->
                          let uu____5956 = mapM fflb lbs1  in
                          bind uu____5956
                            (fun lbs2  ->
                               let uu____5968 = ff e1  in
                               bind uu____5968
                                 (fun e2  ->
                                    let uu____5976 =
                                      FStar_Syntax_Subst.close_let_rec lbs2
                                        e2
                                       in
                                    match uu____5976 with
                                    | (lbs3,e3) ->
                                        ret
                                          (FStar_Syntax_Syntax.Tm_let
                                             ((true, lbs3), e3)))))
                 | FStar_Syntax_Syntax.Tm_ascribed (t2,asc,eff) ->
                     let uu____6042 = ff t2  in
                     bind uu____6042
                       (fun t3  ->
                          ret
                            (FStar_Syntax_Syntax.Tm_ascribed (t3, asc, eff)))
                 | FStar_Syntax_Syntax.Tm_meta (t2,m) ->
                     let uu____6071 = ff t2  in
                     bind uu____6071
                       (fun t3  -> ret (FStar_Syntax_Syntax.Tm_meta (t3, m)))
                 | uu____6076 -> ret tn  in
               bind tn1
                 (fun tn2  ->
                    let t' =
                      let uu___107_6083 = t1  in
                      {
                        FStar_Syntax_Syntax.n = tn2;
                        FStar_Syntax_Syntax.pos =
                          (uu___107_6083.FStar_Syntax_Syntax.pos);
                        FStar_Syntax_Syntax.vars =
                          (uu___107_6083.FStar_Syntax_Syntax.vars)
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
            let uu____6112 = FStar_TypeChecker_TcTerm.tc_term env t  in
            match uu____6112 with
            | (t1,lcomp,g) ->
                let uu____6124 =
                  (let uu____6127 =
                     FStar_Syntax_Util.is_pure_or_ghost_lcomp lcomp  in
                   Prims.op_Negation uu____6127) ||
                    (let uu____6129 = FStar_TypeChecker_Rel.is_trivial g  in
                     Prims.op_Negation uu____6129)
                   in
                if uu____6124
                then ret t1
                else
                  (let rewrite_eq =
                     let typ = lcomp.FStar_Syntax_Syntax.res_typ  in
                     let uu____6139 = new_uvar "pointwise_rec" env typ  in
                     bind uu____6139
                       (fun ut  ->
                          log ps
                            (fun uu____6150  ->
                               let uu____6151 =
                                 FStar_Syntax_Print.term_to_string t1  in
                               let uu____6152 =
                                 FStar_Syntax_Print.term_to_string ut  in
                               FStar_Util.print2
                                 "Pointwise_rec: making equality\n\t%s ==\n\t%s\n"
                                 uu____6151 uu____6152);
                          (let uu____6153 =
                             let uu____6156 =
                               let uu____6157 =
                                 FStar_TypeChecker_TcTerm.universe_of env typ
                                  in
                               FStar_Syntax_Util.mk_eq2 uu____6157 typ t1 ut
                                in
                             add_irrelevant_goal "pointwise_rec equation" env
                               uu____6156 opts
                              in
                           bind uu____6153
                             (fun uu____6160  ->
                                let uu____6161 =
                                  bind tau
                                    (fun uu____6167  ->
                                       let ut1 =
                                         FStar_TypeChecker_Normalize.reduce_uvar_solutions
                                           env ut
                                          in
                                       log ps
                                         (fun uu____6173  ->
                                            let uu____6174 =
                                              FStar_Syntax_Print.term_to_string
                                                t1
                                               in
                                            let uu____6175 =
                                              FStar_Syntax_Print.term_to_string
                                                ut1
                                               in
                                            FStar_Util.print2
                                              "Pointwise_rec: succeeded rewriting\n\t%s to\n\t%s\n"
                                              uu____6174 uu____6175);
                                       ret ut1)
                                   in
                                focus uu____6161)))
                      in
                   let uu____6176 = trytac' rewrite_eq  in
                   bind uu____6176
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
          let uu____6324 = FStar_Syntax_Subst.compress t  in
          maybe_continue ctrl uu____6324
            (fun t1  ->
               let uu____6328 =
                 f env
                   (let uu___111_6337 = t1  in
                    {
                      FStar_Syntax_Syntax.n = (t1.FStar_Syntax_Syntax.n);
                      FStar_Syntax_Syntax.pos =
                        (uu___111_6337.FStar_Syntax_Syntax.pos);
                      FStar_Syntax_Syntax.vars =
                        (uu___111_6337.FStar_Syntax_Syntax.vars)
                    })
                  in
               bind uu____6328
                 (fun uu____6349  ->
                    match uu____6349 with
                    | (t2,ctrl1) ->
                        maybe_continue ctrl1 t2
                          (fun t3  ->
                             let uu____6368 =
                               let uu____6369 =
                                 FStar_Syntax_Subst.compress t3  in
                               uu____6369.FStar_Syntax_Syntax.n  in
                             match uu____6368 with
                             | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
                                 let uu____6402 =
                                   ctrl_tac_fold f env ctrl1 hd1  in
                                 bind uu____6402
                                   (fun uu____6427  ->
                                      match uu____6427 with
                                      | (hd2,ctrl2) ->
                                          let ctrl3 = keep_going ctrl2  in
                                          let uu____6443 =
                                            ctrl_tac_fold_args f env ctrl3
                                              args
                                             in
                                          bind uu____6443
                                            (fun uu____6470  ->
                                               match uu____6470 with
                                               | (args1,ctrl4) ->
                                                   ret
                                                     ((let uu___109_6500 = t3
                                                          in
                                                       {
                                                         FStar_Syntax_Syntax.n
                                                           =
                                                           (FStar_Syntax_Syntax.Tm_app
                                                              (hd2, args1));
                                                         FStar_Syntax_Syntax.pos
                                                           =
                                                           (uu___109_6500.FStar_Syntax_Syntax.pos);
                                                         FStar_Syntax_Syntax.vars
                                                           =
                                                           (uu___109_6500.FStar_Syntax_Syntax.vars)
                                                       }), ctrl4)))
                             | FStar_Syntax_Syntax.Tm_abs (bs,t4,k) ->
                                 let uu____6526 =
                                   FStar_Syntax_Subst.open_term bs t4  in
                                 (match uu____6526 with
                                  | (bs1,t') ->
                                      let uu____6541 =
                                        let uu____6548 =
                                          FStar_TypeChecker_Env.push_binders
                                            env bs1
                                           in
                                        ctrl_tac_fold f uu____6548 ctrl1 t'
                                         in
                                      bind uu____6541
                                        (fun uu____6566  ->
                                           match uu____6566 with
                                           | (t'',ctrl2) ->
                                               let uu____6581 =
                                                 let uu____6588 =
                                                   let uu___110_6591 = t4  in
                                                   let uu____6594 =
                                                     let uu____6595 =
                                                       let uu____6612 =
                                                         FStar_Syntax_Subst.close_binders
                                                           bs1
                                                          in
                                                       let uu____6613 =
                                                         FStar_Syntax_Subst.close
                                                           bs1 t''
                                                          in
                                                       (uu____6612,
                                                         uu____6613, k)
                                                        in
                                                     FStar_Syntax_Syntax.Tm_abs
                                                       uu____6595
                                                      in
                                                   {
                                                     FStar_Syntax_Syntax.n =
                                                       uu____6594;
                                                     FStar_Syntax_Syntax.pos
                                                       =
                                                       (uu___110_6591.FStar_Syntax_Syntax.pos);
                                                     FStar_Syntax_Syntax.vars
                                                       =
                                                       (uu___110_6591.FStar_Syntax_Syntax.vars)
                                                   }  in
                                                 (uu____6588, ctrl2)  in
                                               ret uu____6581))
                             | FStar_Syntax_Syntax.Tm_arrow (bs,k) ->
                                 ret (t3, ctrl1)
                             | uu____6646 -> ret (t3, ctrl1))))

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
              let uu____6697 = ctrl_tac_fold f env ctrl t  in
              bind uu____6697
                (fun uu____6725  ->
                   match uu____6725 with
                   | (t1,ctrl1) ->
                       let uu____6744 = ctrl_tac_fold_args f env ctrl1 ts1
                          in
                       bind uu____6744
                         (fun uu____6775  ->
                            match uu____6775 with
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
              let uu____6859 =
                let uu____6866 =
                  add_irrelevant_goal "dummy" env FStar_Syntax_Util.t_true
                    opts
                   in
                bind uu____6866
                  (fun uu____6875  ->
                     let uu____6876 = ctrl t1  in
                     bind uu____6876
                       (fun res  -> bind trivial (fun uu____6903  -> ret res)))
                 in
              bind uu____6859
                (fun uu____6919  ->
                   match uu____6919 with
                   | (should_rewrite,ctrl1) ->
                       if Prims.op_Negation should_rewrite
                       then ret (t1, ctrl1)
                       else
                         (let uu____6943 =
                            FStar_TypeChecker_TcTerm.tc_term env t1  in
                          match uu____6943 with
                          | (t2,lcomp,g) ->
                              let uu____6959 =
                                (let uu____6962 =
                                   FStar_Syntax_Util.is_pure_or_ghost_lcomp
                                     lcomp
                                    in
                                 Prims.op_Negation uu____6962) ||
                                  (let uu____6964 =
                                     FStar_TypeChecker_Rel.is_trivial g  in
                                   Prims.op_Negation uu____6964)
                                 in
                              if uu____6959
                              then ret (t2, globalStop)
                              else
                                (let typ = lcomp.FStar_Syntax_Syntax.res_typ
                                    in
                                 let uu____6979 =
                                   new_uvar "pointwise_rec" env typ  in
                                 bind uu____6979
                                   (fun ut  ->
                                      log ps
                                        (fun uu____6994  ->
                                           let uu____6995 =
                                             FStar_Syntax_Print.term_to_string
                                               t2
                                              in
                                           let uu____6996 =
                                             FStar_Syntax_Print.term_to_string
                                               ut
                                              in
                                           FStar_Util.print2
                                             "Pointwise_rec: making equality\n\t%s ==\n\t%s\n"
                                             uu____6995 uu____6996);
                                      (let uu____6997 =
                                         let uu____7000 =
                                           let uu____7001 =
                                             FStar_TypeChecker_TcTerm.universe_of
                                               env typ
                                              in
                                           FStar_Syntax_Util.mk_eq2
                                             uu____7001 typ t2 ut
                                            in
                                         add_irrelevant_goal
                                           "rewrite_rec equation" env
                                           uu____7000 opts
                                          in
                                       bind uu____6997
                                         (fun uu____7008  ->
                                            let uu____7009 =
                                              bind rewriter
                                                (fun uu____7023  ->
                                                   let ut1 =
                                                     FStar_TypeChecker_Normalize.reduce_uvar_solutions
                                                       env ut
                                                      in
                                                   log ps
                                                     (fun uu____7029  ->
                                                        let uu____7030 =
                                                          FStar_Syntax_Print.term_to_string
                                                            t2
                                                           in
                                                        let uu____7031 =
                                                          FStar_Syntax_Print.term_to_string
                                                            ut1
                                                           in
                                                        FStar_Util.print2
                                                          "rewrite_rec: succeeded rewriting\n\t%s to\n\t%s\n"
                                                          uu____7030
                                                          uu____7031);
                                                   ret (ut1, ctrl1))
                                               in
                                            focus uu____7009))))))
  
let (topdown_rewrite :
  (FStar_Syntax_Syntax.term ->
     (Prims.bool,FStar_BigInt.t) FStar_Pervasives_Native.tuple2 tac)
    -> Prims.unit tac -> Prims.unit tac)
  =
  fun ctrl  ->
    fun rewriter  ->
      bind get
        (fun ps  ->
           let uu____7075 =
             match ps.FStar_Tactics_Types.goals with
             | g::gs -> (g, gs)
             | [] -> failwith "Pointwise: no goals"  in
           match uu____7075 with
           | (g,gs) ->
               let gt1 = g.FStar_Tactics_Types.goal_ty  in
               (log ps
                  (fun uu____7112  ->
                     let uu____7113 = FStar_Syntax_Print.term_to_string gt1
                        in
                     FStar_Util.print1 "Pointwise starting with %s\n"
                       uu____7113);
                bind dismiss_all
                  (fun uu____7116  ->
                     let uu____7117 =
                       ctrl_tac_fold
                         (rewrite_rec ps ctrl rewriter
                            g.FStar_Tactics_Types.opts)
                         g.FStar_Tactics_Types.context keepGoing gt1
                        in
                     bind uu____7117
                       (fun uu____7135  ->
                          match uu____7135 with
                          | (gt',uu____7143) ->
                              (log ps
                                 (fun uu____7147  ->
                                    let uu____7148 =
                                      FStar_Syntax_Print.term_to_string gt'
                                       in
                                    FStar_Util.print1
                                      "Pointwise seems to have succeded with %s\n"
                                      uu____7148);
                               (let uu____7149 = push_goals gs  in
                                bind uu____7149
                                  (fun uu____7153  ->
                                     add_goals
                                       [(let uu___112_7155 = g  in
                                         {
                                           FStar_Tactics_Types.context =
                                             (uu___112_7155.FStar_Tactics_Types.context);
                                           FStar_Tactics_Types.witness =
                                             (uu___112_7155.FStar_Tactics_Types.witness);
                                           FStar_Tactics_Types.goal_ty = gt';
                                           FStar_Tactics_Types.opts =
                                             (uu___112_7155.FStar_Tactics_Types.opts);
                                           FStar_Tactics_Types.is_guard =
                                             (uu___112_7155.FStar_Tactics_Types.is_guard)
                                         })])))))))
  
let (pointwise :
  FStar_Tactics_Types.direction -> Prims.unit tac -> Prims.unit tac) =
  fun d  ->
    fun tau  ->
      bind get
        (fun ps  ->
           let uu____7177 =
             match ps.FStar_Tactics_Types.goals with
             | g::gs -> (g, gs)
             | [] -> failwith "Pointwise: no goals"  in
           match uu____7177 with
           | (g,gs) ->
               let gt1 = g.FStar_Tactics_Types.goal_ty  in
               (log ps
                  (fun uu____7214  ->
                     let uu____7215 = FStar_Syntax_Print.term_to_string gt1
                        in
                     FStar_Util.print1 "Pointwise starting with %s\n"
                       uu____7215);
                bind dismiss_all
                  (fun uu____7218  ->
                     let uu____7219 =
                       tac_fold_env d
                         (pointwise_rec ps tau g.FStar_Tactics_Types.opts)
                         g.FStar_Tactics_Types.context gt1
                        in
                     bind uu____7219
                       (fun gt'  ->
                          log ps
                            (fun uu____7229  ->
                               let uu____7230 =
                                 FStar_Syntax_Print.term_to_string gt'  in
                               FStar_Util.print1
                                 "Pointwise seems to have succeded with %s\n"
                                 uu____7230);
                          (let uu____7231 = push_goals gs  in
                           bind uu____7231
                             (fun uu____7235  ->
                                add_goals
                                  [(let uu___113_7237 = g  in
                                    {
                                      FStar_Tactics_Types.context =
                                        (uu___113_7237.FStar_Tactics_Types.context);
                                      FStar_Tactics_Types.witness =
                                        (uu___113_7237.FStar_Tactics_Types.witness);
                                      FStar_Tactics_Types.goal_ty = gt';
                                      FStar_Tactics_Types.opts =
                                        (uu___113_7237.FStar_Tactics_Types.opts);
                                      FStar_Tactics_Types.is_guard =
                                        (uu___113_7237.FStar_Tactics_Types.is_guard)
                                    })]))))))
  
let (trefl : Prims.unit tac) =
  bind cur_goal
    (fun g  ->
       let uu____7257 =
         FStar_Syntax_Util.un_squash g.FStar_Tactics_Types.goal_ty  in
       match uu____7257 with
       | FStar_Pervasives_Native.Some t ->
           let uu____7269 = FStar_Syntax_Util.head_and_args' t  in
           (match uu____7269 with
            | (hd1,args) ->
                let uu____7302 =
                  let uu____7315 =
                    let uu____7316 = FStar_Syntax_Util.un_uinst hd1  in
                    uu____7316.FStar_Syntax_Syntax.n  in
                  (uu____7315, args)  in
                (match uu____7302 with
                 | (FStar_Syntax_Syntax.Tm_fvar
                    fv,uu____7330::(l,uu____7332)::(r,uu____7334)::[]) when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.eq2_lid
                     ->
                     let uu____7381 =
                       do_unify g.FStar_Tactics_Types.context l r  in
                     bind uu____7381
                       (fun b  ->
                          if Prims.op_Negation b
                          then
                            let uu____7390 =
                              tts g.FStar_Tactics_Types.context l  in
                            let uu____7391 =
                              tts g.FStar_Tactics_Types.context r  in
                            fail2 "trefl: not a trivial equality (%s vs %s)"
                              uu____7390 uu____7391
                          else solve g FStar_Syntax_Util.exp_unit)
                 | (hd2,uu____7394) ->
                     let uu____7411 = tts g.FStar_Tactics_Types.context t  in
                     fail1 "trefl: not an equality (%s)" uu____7411))
       | FStar_Pervasives_Native.None  -> fail "not an irrelevant goal")
  
let (dup : Prims.unit tac) =
  bind cur_goal
    (fun g  ->
       let uu____7421 =
         new_uvar "dup" g.FStar_Tactics_Types.context
           g.FStar_Tactics_Types.goal_ty
          in
       bind uu____7421
         (fun u  ->
            let g' =
              let uu___114_7428 = g  in
              {
                FStar_Tactics_Types.context =
                  (uu___114_7428.FStar_Tactics_Types.context);
                FStar_Tactics_Types.witness = u;
                FStar_Tactics_Types.goal_ty =
                  (uu___114_7428.FStar_Tactics_Types.goal_ty);
                FStar_Tactics_Types.opts =
                  (uu___114_7428.FStar_Tactics_Types.opts);
                FStar_Tactics_Types.is_guard =
                  (uu___114_7428.FStar_Tactics_Types.is_guard)
              }  in
            bind __dismiss
              (fun uu____7431  ->
                 let uu____7432 =
                   let uu____7435 =
                     let uu____7436 =
                       FStar_TypeChecker_TcTerm.universe_of
                         g.FStar_Tactics_Types.context
                         g.FStar_Tactics_Types.goal_ty
                        in
                     FStar_Syntax_Util.mk_eq2 uu____7436
                       g.FStar_Tactics_Types.goal_ty u
                       g.FStar_Tactics_Types.witness
                      in
                   add_irrelevant_goal "dup equation"
                     g.FStar_Tactics_Types.context uu____7435
                     g.FStar_Tactics_Types.opts
                    in
                 bind uu____7432
                   (fun uu____7439  ->
                      let uu____7440 = add_goals [g']  in
                      bind uu____7440 (fun uu____7444  -> ret ())))))
  
let (flip : Prims.unit tac) =
  bind get
    (fun ps  ->
       match ps.FStar_Tactics_Types.goals with
       | g1::g2::gs ->
           set
             (let uu___115_7463 = ps  in
              {
                FStar_Tactics_Types.main_context =
                  (uu___115_7463.FStar_Tactics_Types.main_context);
                FStar_Tactics_Types.main_goal =
                  (uu___115_7463.FStar_Tactics_Types.main_goal);
                FStar_Tactics_Types.all_implicits =
                  (uu___115_7463.FStar_Tactics_Types.all_implicits);
                FStar_Tactics_Types.goals = (g2 :: g1 :: gs);
                FStar_Tactics_Types.smt_goals =
                  (uu___115_7463.FStar_Tactics_Types.smt_goals);
                FStar_Tactics_Types.depth =
                  (uu___115_7463.FStar_Tactics_Types.depth);
                FStar_Tactics_Types.__dump =
                  (uu___115_7463.FStar_Tactics_Types.__dump);
                FStar_Tactics_Types.psc =
                  (uu___115_7463.FStar_Tactics_Types.psc);
                FStar_Tactics_Types.entry_range =
                  (uu___115_7463.FStar_Tactics_Types.entry_range);
                FStar_Tactics_Types.guard_policy =
                  (uu___115_7463.FStar_Tactics_Types.guard_policy)
              })
       | uu____7464 -> fail "flip: less than 2 goals")
  
let (later : Prims.unit tac) =
  bind get
    (fun ps  ->
       match ps.FStar_Tactics_Types.goals with
       | [] -> ret ()
       | g::gs ->
           set
             (let uu___116_7481 = ps  in
              {
                FStar_Tactics_Types.main_context =
                  (uu___116_7481.FStar_Tactics_Types.main_context);
                FStar_Tactics_Types.main_goal =
                  (uu___116_7481.FStar_Tactics_Types.main_goal);
                FStar_Tactics_Types.all_implicits =
                  (uu___116_7481.FStar_Tactics_Types.all_implicits);
                FStar_Tactics_Types.goals = (FStar_List.append gs [g]);
                FStar_Tactics_Types.smt_goals =
                  (uu___116_7481.FStar_Tactics_Types.smt_goals);
                FStar_Tactics_Types.depth =
                  (uu___116_7481.FStar_Tactics_Types.depth);
                FStar_Tactics_Types.__dump =
                  (uu___116_7481.FStar_Tactics_Types.__dump);
                FStar_Tactics_Types.psc =
                  (uu___116_7481.FStar_Tactics_Types.psc);
                FStar_Tactics_Types.entry_range =
                  (uu___116_7481.FStar_Tactics_Types.entry_range);
                FStar_Tactics_Types.guard_policy =
                  (uu___116_7481.FStar_Tactics_Types.guard_policy)
              }))
  
let (qed : Prims.unit tac) =
  bind get
    (fun ps  ->
       match ps.FStar_Tactics_Types.goals with
       | [] -> ret ()
       | uu____7490 -> fail "Not done!")
  
let (cases :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 tac)
  =
  fun t  ->
    let uu____7508 =
      bind cur_goal
        (fun g  ->
           let uu____7522 = __tc g.FStar_Tactics_Types.context t  in
           bind uu____7522
             (fun uu____7558  ->
                match uu____7558 with
                | (t1,typ,guard) ->
                    let uu____7574 = FStar_Syntax_Util.head_and_args typ  in
                    (match uu____7574 with
                     | (hd1,args) ->
                         let uu____7617 =
                           let uu____7630 =
                             let uu____7631 = FStar_Syntax_Util.un_uinst hd1
                                in
                             uu____7631.FStar_Syntax_Syntax.n  in
                           (uu____7630, args)  in
                         (match uu____7617 with
                          | (FStar_Syntax_Syntax.Tm_fvar
                             fv,(p,uu____7650)::(q,uu____7652)::[]) when
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
                                let uu___117_7690 = g  in
                                let uu____7691 =
                                  FStar_TypeChecker_Env.push_bv
                                    g.FStar_Tactics_Types.context v_p
                                   in
                                {
                                  FStar_Tactics_Types.context = uu____7691;
                                  FStar_Tactics_Types.witness =
                                    (uu___117_7690.FStar_Tactics_Types.witness);
                                  FStar_Tactics_Types.goal_ty =
                                    (uu___117_7690.FStar_Tactics_Types.goal_ty);
                                  FStar_Tactics_Types.opts =
                                    (uu___117_7690.FStar_Tactics_Types.opts);
                                  FStar_Tactics_Types.is_guard =
                                    (uu___117_7690.FStar_Tactics_Types.is_guard)
                                }  in
                              let g2 =
                                let uu___118_7693 = g  in
                                let uu____7694 =
                                  FStar_TypeChecker_Env.push_bv
                                    g.FStar_Tactics_Types.context v_q
                                   in
                                {
                                  FStar_Tactics_Types.context = uu____7694;
                                  FStar_Tactics_Types.witness =
                                    (uu___118_7693.FStar_Tactics_Types.witness);
                                  FStar_Tactics_Types.goal_ty =
                                    (uu___118_7693.FStar_Tactics_Types.goal_ty);
                                  FStar_Tactics_Types.opts =
                                    (uu___118_7693.FStar_Tactics_Types.opts);
                                  FStar_Tactics_Types.is_guard =
                                    (uu___118_7693.FStar_Tactics_Types.is_guard)
                                }  in
                              bind __dismiss
                                (fun uu____7701  ->
                                   let uu____7702 = add_goals [g1; g2]  in
                                   bind uu____7702
                                     (fun uu____7711  ->
                                        let uu____7712 =
                                          let uu____7717 =
                                            FStar_Syntax_Syntax.bv_to_name
                                              v_p
                                             in
                                          let uu____7718 =
                                            FStar_Syntax_Syntax.bv_to_name
                                              v_q
                                             in
                                          (uu____7717, uu____7718)  in
                                        ret uu____7712))
                          | uu____7723 ->
                              let uu____7736 =
                                tts g.FStar_Tactics_Types.context typ  in
                              fail1 "Not a disjunction: %s" uu____7736))))
       in
    FStar_All.pipe_left (wrap_err "cases") uu____7508
  
let (set_options : Prims.string -> Prims.unit tac) =
  fun s  ->
    bind cur_goal
      (fun g  ->
         FStar_Options.push ();
         (let uu____7774 = FStar_Util.smap_copy g.FStar_Tactics_Types.opts
             in
          FStar_Options.set uu____7774);
         (let res = FStar_Options.set_options FStar_Options.Set s  in
          let opts' = FStar_Options.peek ()  in
          FStar_Options.pop ();
          (match res with
           | FStar_Getopt.Success  ->
               let g' =
                 let uu___119_7781 = g  in
                 {
                   FStar_Tactics_Types.context =
                     (uu___119_7781.FStar_Tactics_Types.context);
                   FStar_Tactics_Types.witness =
                     (uu___119_7781.FStar_Tactics_Types.witness);
                   FStar_Tactics_Types.goal_ty =
                     (uu___119_7781.FStar_Tactics_Types.goal_ty);
                   FStar_Tactics_Types.opts = opts';
                   FStar_Tactics_Types.is_guard =
                     (uu___119_7781.FStar_Tactics_Types.is_guard)
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
      let uu____7825 =
        bind cur_goal
          (fun goal  ->
             let env =
               FStar_TypeChecker_Env.set_expected_typ
                 goal.FStar_Tactics_Types.context ty
                in
             let uu____7833 = __tc env tm  in
             bind uu____7833
               (fun uu____7853  ->
                  match uu____7853 with
                  | (tm1,typ,guard) ->
                      let uu____7865 =
                        proc_guard "unquote" env guard
                          goal.FStar_Tactics_Types.opts
                         in
                      bind uu____7865 (fun uu____7869  -> ret tm1)))
         in
      FStar_All.pipe_left (wrap_err "unquote") uu____7825
  
let (uvar_env :
  env ->
    FStar_Syntax_Syntax.typ FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.term tac)
  =
  fun env  ->
    fun ty  ->
      let uu____7888 =
        match ty with
        | FStar_Pervasives_Native.Some ty1 -> ret ty1
        | FStar_Pervasives_Native.None  ->
            let uu____7894 =
              let uu____7895 = FStar_Syntax_Util.type_u ()  in
              FStar_All.pipe_left FStar_Pervasives_Native.fst uu____7895  in
            new_uvar "uvar_env.2" env uu____7894
         in
      bind uu____7888
        (fun typ  ->
           let uu____7907 = new_uvar "uvar_env" env typ  in
           bind uu____7907 (fun t  -> ret t))
  
let (unshelve : FStar_Syntax_Syntax.term -> Prims.unit tac) =
  fun t  ->
    let uu____7919 =
      bind get
        (fun ps  ->
           let env = ps.FStar_Tactics_Types.main_context  in
           let opts =
             match ps.FStar_Tactics_Types.goals with
             | g::uu____7930 -> g.FStar_Tactics_Types.opts
             | uu____7933 -> FStar_Options.peek ()  in
           let uu____7936 = __tc env t  in
           bind uu____7936
             (fun uu____7956  ->
                match uu____7956 with
                | (t1,typ,guard) ->
                    let uu____7968 = proc_guard "unshelve" env guard opts  in
                    bind uu____7968
                      (fun uu____7973  ->
                         let uu____7974 =
                           let uu____7977 =
                             let uu____7978 = bnorm env t1  in
                             let uu____7979 = bnorm env typ  in
                             {
                               FStar_Tactics_Types.context = env;
                               FStar_Tactics_Types.witness = uu____7978;
                               FStar_Tactics_Types.goal_ty = uu____7979;
                               FStar_Tactics_Types.opts = opts;
                               FStar_Tactics_Types.is_guard = false
                             }  in
                           [uu____7977]  in
                         add_goals uu____7974)))
       in
    FStar_All.pipe_left (wrap_err "unshelve") uu____7919
  
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
          (fun uu____8012  ->
             let uu____8013 = FStar_Options.unsafe_tactic_exec ()  in
             if uu____8013
             then
               let s =
                 FStar_Util.launch_process true "tactic_launch" prog args
                   input (fun uu____8019  -> fun uu____8020  -> false)
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
        (fun uu____8034  ->
           let uu____8035 =
             FStar_Syntax_Syntax.gen_bv nm FStar_Pervasives_Native.None t  in
           ret uu____8035)
  
let (change : FStar_Syntax_Syntax.typ -> Prims.unit tac) =
  fun ty  ->
    let uu____8043 =
      mlog
        (fun uu____8048  ->
           let uu____8049 = FStar_Syntax_Print.term_to_string ty  in
           FStar_Util.print1 "change: ty = %s\n" uu____8049)
        (fun uu____8051  ->
           bind cur_goal
             (fun g  ->
                let uu____8055 = __tc g.FStar_Tactics_Types.context ty  in
                bind uu____8055
                  (fun uu____8075  ->
                     match uu____8075 with
                     | (ty1,uu____8085,guard) ->
                         let uu____8087 =
                           proc_guard "change" g.FStar_Tactics_Types.context
                             guard g.FStar_Tactics_Types.opts
                            in
                         bind uu____8087
                           (fun uu____8092  ->
                              let uu____8093 =
                                do_unify g.FStar_Tactics_Types.context
                                  g.FStar_Tactics_Types.goal_ty ty1
                                 in
                              bind uu____8093
                                (fun bb  ->
                                   if bb
                                   then
                                     replace_cur
                                       (let uu___120_8102 = g  in
                                        {
                                          FStar_Tactics_Types.context =
                                            (uu___120_8102.FStar_Tactics_Types.context);
                                          FStar_Tactics_Types.witness =
                                            (uu___120_8102.FStar_Tactics_Types.witness);
                                          FStar_Tactics_Types.goal_ty = ty1;
                                          FStar_Tactics_Types.opts =
                                            (uu___120_8102.FStar_Tactics_Types.opts);
                                          FStar_Tactics_Types.is_guard =
                                            (uu___120_8102.FStar_Tactics_Types.is_guard)
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
                                      let uu____8109 =
                                        do_unify
                                          g.FStar_Tactics_Types.context ng
                                          nty
                                         in
                                      bind uu____8109
                                        (fun b  ->
                                           if b
                                           then
                                             replace_cur
                                               (let uu___121_8118 = g  in
                                                {
                                                  FStar_Tactics_Types.context
                                                    =
                                                    (uu___121_8118.FStar_Tactics_Types.context);
                                                  FStar_Tactics_Types.witness
                                                    =
                                                    (uu___121_8118.FStar_Tactics_Types.witness);
                                                  FStar_Tactics_Types.goal_ty
                                                    = ty1;
                                                  FStar_Tactics_Types.opts =
                                                    (uu___121_8118.FStar_Tactics_Types.opts);
                                                  FStar_Tactics_Types.is_guard
                                                    =
                                                    (uu___121_8118.FStar_Tactics_Types.is_guard)
                                                })
                                           else fail "not convertible")))))))
       in
    FStar_All.pipe_left (wrap_err "change") uu____8043
  
let (goal_of_goal_ty :
  env ->
    FStar_Syntax_Syntax.typ ->
      (FStar_Tactics_Types.goal,FStar_TypeChecker_Env.guard_t)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun typ  ->
      let uu____8138 =
        FStar_TypeChecker_Util.new_implicit_var "proofstate_of_goal_ty"
          typ.FStar_Syntax_Syntax.pos env typ
         in
      match uu____8138 with
      | (u,uu____8156,g_u) ->
          let g =
            let uu____8171 = FStar_Options.peek ()  in
            {
              FStar_Tactics_Types.context = env;
              FStar_Tactics_Types.witness = u;
              FStar_Tactics_Types.goal_ty = typ;
              FStar_Tactics_Types.opts = uu____8171;
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
      let uu____8182 = goal_of_goal_ty env typ  in
      match uu____8182 with
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
  