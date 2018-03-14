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
  
let (comp_to_typ : FStar_Syntax_Syntax.comp -> FStar_Reflection_Data.typ) =
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
         let uu___67_1095 = p  in
         let uu____1096 = FStar_List.tl p.FStar_Tactics_Types.goals  in
         {
           FStar_Tactics_Types.main_context =
             (uu___67_1095.FStar_Tactics_Types.main_context);
           FStar_Tactics_Types.main_goal =
             (uu___67_1095.FStar_Tactics_Types.main_goal);
           FStar_Tactics_Types.all_implicits =
             (uu___67_1095.FStar_Tactics_Types.all_implicits);
           FStar_Tactics_Types.goals = uu____1096;
           FStar_Tactics_Types.smt_goals =
             (uu___67_1095.FStar_Tactics_Types.smt_goals);
           FStar_Tactics_Types.depth =
             (uu___67_1095.FStar_Tactics_Types.depth);
           FStar_Tactics_Types.__dump =
             (uu___67_1095.FStar_Tactics_Types.__dump);
           FStar_Tactics_Types.psc = (uu___67_1095.FStar_Tactics_Types.psc);
           FStar_Tactics_Types.entry_range =
             (uu___67_1095.FStar_Tactics_Types.entry_range);
           FStar_Tactics_Types.guard_policy =
             (uu___67_1095.FStar_Tactics_Types.guard_policy)
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
         (let uu___68_1138 = p  in
          {
            FStar_Tactics_Types.main_context =
              (uu___68_1138.FStar_Tactics_Types.main_context);
            FStar_Tactics_Types.main_goal =
              (uu___68_1138.FStar_Tactics_Types.main_goal);
            FStar_Tactics_Types.all_implicits =
              (uu___68_1138.FStar_Tactics_Types.all_implicits);
            FStar_Tactics_Types.goals = [];
            FStar_Tactics_Types.smt_goals =
              (uu___68_1138.FStar_Tactics_Types.smt_goals);
            FStar_Tactics_Types.depth =
              (uu___68_1138.FStar_Tactics_Types.depth);
            FStar_Tactics_Types.__dump =
              (uu___68_1138.FStar_Tactics_Types.__dump);
            FStar_Tactics_Types.psc = (uu___68_1138.FStar_Tactics_Types.psc);
            FStar_Tactics_Types.entry_range =
              (uu___68_1138.FStar_Tactics_Types.entry_range);
            FStar_Tactics_Types.guard_policy =
              (uu___68_1138.FStar_Tactics_Types.guard_policy)
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
           (let uu___69_1277 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___69_1277.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___69_1277.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___69_1277.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (FStar_List.append gs p.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___69_1277.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___69_1277.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___69_1277.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___69_1277.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___69_1277.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___69_1277.FStar_Tactics_Types.guard_policy)
            }))
  
let (add_smt_goals : FStar_Tactics_Types.goal Prims.list -> Prims.unit tac) =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___70_1295 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___70_1295.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___70_1295.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___70_1295.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___70_1295.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (FStar_List.append gs p.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___70_1295.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___70_1295.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___70_1295.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___70_1295.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___70_1295.FStar_Tactics_Types.guard_policy)
            }))
  
let (push_goals : FStar_Tactics_Types.goal Prims.list -> Prims.unit tac) =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___71_1313 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___71_1313.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___71_1313.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___71_1313.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (FStar_List.append p.FStar_Tactics_Types.goals gs);
              FStar_Tactics_Types.smt_goals =
                (uu___71_1313.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___71_1313.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___71_1313.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___71_1313.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___71_1313.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___71_1313.FStar_Tactics_Types.guard_policy)
            }))
  
let (push_smt_goals : FStar_Tactics_Types.goal Prims.list -> Prims.unit tac)
  =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___72_1331 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___72_1331.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___72_1331.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___72_1331.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___72_1331.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (FStar_List.append p.FStar_Tactics_Types.smt_goals gs);
              FStar_Tactics_Types.depth =
                (uu___72_1331.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___72_1331.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___72_1331.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___72_1331.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___72_1331.FStar_Tactics_Types.guard_policy)
            }))
  
let (replace_cur : FStar_Tactics_Types.goal -> Prims.unit tac) =
  fun g  -> bind __dismiss (fun uu____1340  -> add_goals [g]) 
let (add_implicits : implicits -> Prims.unit tac) =
  fun i  ->
    bind get
      (fun p  ->
         set
           (let uu___73_1352 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___73_1352.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___73_1352.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (FStar_List.append i p.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___73_1352.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___73_1352.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___73_1352.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___73_1352.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___73_1352.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___73_1352.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___73_1352.FStar_Tactics_Types.guard_policy)
            }))
  
let (new_uvar :
  Prims.string ->
    env -> FStar_Reflection_Data.typ -> FStar_Syntax_Syntax.term tac)
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
  
let (admit : Prims.unit tac) =
  let uu____1475 =
    bind cur_goal
      (fun g  ->
         (let uu____1482 =
            let uu____1487 =
              let uu____1488 = goal_to_string g  in
              FStar_Util.format1 "Tactics admitted goal <%s>\n\n" uu____1488
               in
            (FStar_Errors.Warning_TacAdmit, uu____1487)  in
          FStar_Errors.log_issue
            (g.FStar_Tactics_Types.goal_ty).FStar_Syntax_Syntax.pos
            uu____1482);
         solve g FStar_Syntax_Util.exp_unit)
     in
  FStar_All.pipe_left (wrap_err "admit") uu____1475 
let (ngoals : FStar_BigInt.bigint tac) =
  bind get
    (fun ps  ->
       let n1 = FStar_List.length ps.FStar_Tactics_Types.goals  in
       let uu____1502 = FStar_BigInt.of_int_fs n1  in ret uu____1502)
  
let (ngoals_smt : FStar_BigInt.bigint tac) =
  bind get
    (fun ps  ->
       let n1 = FStar_List.length ps.FStar_Tactics_Types.smt_goals  in
       let uu____1518 = FStar_BigInt.of_int_fs n1  in ret uu____1518)
  
let (is_guard : Prims.bool tac) =
  bind cur_goal (fun g  -> ret g.FStar_Tactics_Types.is_guard) 
let (mk_irrelevant_goal :
  Prims.string ->
    env ->
      FStar_Reflection_Data.typ ->
        FStar_Options.optionstate -> FStar_Tactics_Types.goal tac)
  =
  fun reason  ->
    fun env  ->
      fun phi  ->
        fun opts  ->
          let typ =
            let uu____1550 = env.FStar_TypeChecker_Env.universe_of env phi
               in
            FStar_Syntax_Util.mk_squash uu____1550 phi  in
          let uu____1551 = new_uvar reason env typ  in
          bind uu____1551
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
      (FStar_Syntax_Syntax.term,FStar_Reflection_Data.typ,FStar_TypeChecker_Env.guard_t)
        FStar_Pervasives_Native.tuple3 tac)
  =
  fun e  ->
    fun t  ->
      bind get
        (fun ps  ->
           try
             let uu____1607 =
               (ps.FStar_Tactics_Types.main_context).FStar_TypeChecker_Env.type_of
                 e t
                in
             ret uu____1607
           with
           | FStar_Errors.Err (uu____1634,msg) ->
               let uu____1636 = tts e t  in
               let uu____1637 =
                 let uu____1638 = FStar_TypeChecker_Env.all_binders e  in
                 FStar_All.pipe_right uu____1638
                   (FStar_Syntax_Print.binders_to_string ", ")
                  in
               fail3 "Cannot type %s in context (%s). Error = (%s)"
                 uu____1636 uu____1637 msg
           | FStar_Errors.Error (uu____1645,msg,uu____1647) ->
               let uu____1648 = tts e t  in
               let uu____1649 =
                 let uu____1650 = FStar_TypeChecker_Env.all_binders e  in
                 FStar_All.pipe_right uu____1650
                   (FStar_Syntax_Print.binders_to_string ", ")
                  in
               fail3 "Cannot type %s in context (%s). Error = (%s)"
                 uu____1648 uu____1649 msg)
  
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
           (let uu___76_1684 = ps  in
            {
              FStar_Tactics_Types.main_context =
                (uu___76_1684.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___76_1684.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___76_1684.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___76_1684.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___76_1684.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___76_1684.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___76_1684.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___76_1684.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___76_1684.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy = pol
            }))
  
let with_policy : 'a . FStar_Tactics_Types.guard_policy -> 'a tac -> 'a tac =
  fun pol  ->
    fun t  ->
      bind get_guard_policy
        (fun old_pol  ->
           let uu____1706 = set_guard_policy pol  in
           bind uu____1706
             (fun uu____1710  ->
                bind t
                  (fun r  ->
                     let uu____1714 = set_guard_policy old_pol  in
                     bind uu____1714 (fun uu____1718  -> ret r))))
  
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
          let uu____1735 =
            let uu____1736 = FStar_TypeChecker_Rel.simplify_guard e g  in
            uu____1736.FStar_TypeChecker_Env.guard_f  in
          match uu____1735 with
          | FStar_TypeChecker_Common.Trivial  -> ret ()
          | FStar_TypeChecker_Common.NonTrivial f ->
              let uu____1740 = istrivial e f  in
              if uu____1740
              then ret ()
              else
                bind get
                  (fun ps  ->
                     match ps.FStar_Tactics_Types.guard_policy with
                     | FStar_Tactics_Types.Drop  -> ret ()
                     | FStar_Tactics_Types.Goal  ->
                         let uu____1748 = mk_irrelevant_goal reason e f opts
                            in
                         bind uu____1748
                           (fun goal  ->
                              let goal1 =
                                let uu___77_1755 = goal  in
                                {
                                  FStar_Tactics_Types.context =
                                    (uu___77_1755.FStar_Tactics_Types.context);
                                  FStar_Tactics_Types.witness =
                                    (uu___77_1755.FStar_Tactics_Types.witness);
                                  FStar_Tactics_Types.goal_ty =
                                    (uu___77_1755.FStar_Tactics_Types.goal_ty);
                                  FStar_Tactics_Types.opts =
                                    (uu___77_1755.FStar_Tactics_Types.opts);
                                  FStar_Tactics_Types.is_guard = true
                                }  in
                              push_goals [goal1])
                     | FStar_Tactics_Types.SMT  ->
                         let uu____1756 = mk_irrelevant_goal reason e f opts
                            in
                         bind uu____1756
                           (fun goal  ->
                              let goal1 =
                                let uu___78_1763 = goal  in
                                {
                                  FStar_Tactics_Types.context =
                                    (uu___78_1763.FStar_Tactics_Types.context);
                                  FStar_Tactics_Types.witness =
                                    (uu___78_1763.FStar_Tactics_Types.witness);
                                  FStar_Tactics_Types.goal_ty =
                                    (uu___78_1763.FStar_Tactics_Types.goal_ty);
                                  FStar_Tactics_Types.opts =
                                    (uu___78_1763.FStar_Tactics_Types.opts);
                                  FStar_Tactics_Types.is_guard = true
                                }  in
                              push_smt_goals [goal1])
                     | FStar_Tactics_Types.Force  ->
                         (try
                            let uu____1771 =
                              let uu____1772 =
                                let uu____1773 =
                                  FStar_TypeChecker_Rel.discharge_guard_no_smt
                                    e g
                                   in
                                FStar_All.pipe_left
                                  FStar_TypeChecker_Rel.is_trivial uu____1773
                                 in
                              Prims.op_Negation uu____1772  in
                            if uu____1771
                            then
                              mlog
                                (fun uu____1778  ->
                                   let uu____1779 =
                                     FStar_TypeChecker_Rel.guard_to_string e
                                       g
                                      in
                                   FStar_Util.print1 "guard = %s\n"
                                     uu____1779)
                                (fun uu____1781  ->
                                   fail1 "Forcing the guard failed %s)"
                                     reason)
                            else ret ()
                          with
                          | uu____1788 ->
                              mlog
                                (fun uu____1791  ->
                                   let uu____1792 =
                                     FStar_TypeChecker_Rel.guard_to_string e
                                       g
                                      in
                                   FStar_Util.print1 "guard = %s\n"
                                     uu____1792)
                                (fun uu____1794  ->
                                   fail1 "Forcing the guard failed (%s)"
                                     reason)))
  
let (tc : FStar_Syntax_Syntax.term -> FStar_Reflection_Data.typ tac) =
  fun t  ->
    let uu____1802 =
      bind cur_goal
        (fun goal  ->
           let uu____1808 = __tc goal.FStar_Tactics_Types.context t  in
           bind uu____1808
             (fun uu____1828  ->
                match uu____1828 with
                | (t1,typ,guard) ->
                    let uu____1840 =
                      proc_guard "tc" goal.FStar_Tactics_Types.context guard
                        goal.FStar_Tactics_Types.opts
                       in
                    bind uu____1840 (fun uu____1844  -> ret typ)))
       in
    FStar_All.pipe_left (wrap_err "tc") uu____1802
  
let (add_irrelevant_goal :
  Prims.string ->
    env ->
      FStar_Reflection_Data.typ ->
        FStar_Options.optionstate -> Prims.unit tac)
  =
  fun reason  ->
    fun env  ->
      fun phi  ->
        fun opts  ->
          let uu____1865 = mk_irrelevant_goal reason env phi opts  in
          bind uu____1865 (fun goal  -> add_goals [goal])
  
let (trivial : Prims.unit tac) =
  bind cur_goal
    (fun goal  ->
       let uu____1877 =
         istrivial goal.FStar_Tactics_Types.context
           goal.FStar_Tactics_Types.goal_ty
          in
       if uu____1877
       then solve goal FStar_Syntax_Util.exp_unit
       else
         (let uu____1881 =
            tts goal.FStar_Tactics_Types.context
              goal.FStar_Tactics_Types.goal_ty
             in
          fail1 "Not a trivial goal: %s" uu____1881))
  
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
          let uu____1902 =
            let uu____1903 = FStar_TypeChecker_Rel.simplify_guard e g  in
            uu____1903.FStar_TypeChecker_Env.guard_f  in
          match uu____1902 with
          | FStar_TypeChecker_Common.Trivial  ->
              ret FStar_Pervasives_Native.None
          | FStar_TypeChecker_Common.NonTrivial f ->
              let uu____1911 = istrivial e f  in
              if uu____1911
              then ret FStar_Pervasives_Native.None
              else
                (let uu____1919 = mk_irrelevant_goal reason e f opts  in
                 bind uu____1919
                   (fun goal  ->
                      ret
                        (FStar_Pervasives_Native.Some
                           (let uu___81_1929 = goal  in
                            {
                              FStar_Tactics_Types.context =
                                (uu___81_1929.FStar_Tactics_Types.context);
                              FStar_Tactics_Types.witness =
                                (uu___81_1929.FStar_Tactics_Types.witness);
                              FStar_Tactics_Types.goal_ty =
                                (uu___81_1929.FStar_Tactics_Types.goal_ty);
                              FStar_Tactics_Types.opts =
                                (uu___81_1929.FStar_Tactics_Types.opts);
                              FStar_Tactics_Types.is_guard = true
                            }))))
  
let (smt : Prims.unit tac) =
  bind cur_goal
    (fun g  ->
       let uu____1937 = is_irrelevant g  in
       if uu____1937
       then bind __dismiss (fun uu____1941  -> add_smt_goals [g])
       else
         (let uu____1943 =
            tts g.FStar_Tactics_Types.context g.FStar_Tactics_Types.goal_ty
             in
          fail1 "goal is not irrelevant: cannot dispatch to smt (%s)"
            uu____1943))
  
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
             let uu____1984 =
               try
                 let uu____2018 =
                   let uu____2027 = FStar_BigInt.to_int_fs n1  in
                   FStar_List.splitAt uu____2027 p.FStar_Tactics_Types.goals
                    in
                 ret uu____2018
               with | uu____2049 -> fail "divide: not enough goals"  in
             bind uu____1984
               (fun uu____2076  ->
                  match uu____2076 with
                  | (lgs,rgs) ->
                      let lp =
                        let uu___82_2102 = p  in
                        {
                          FStar_Tactics_Types.main_context =
                            (uu___82_2102.FStar_Tactics_Types.main_context);
                          FStar_Tactics_Types.main_goal =
                            (uu___82_2102.FStar_Tactics_Types.main_goal);
                          FStar_Tactics_Types.all_implicits =
                            (uu___82_2102.FStar_Tactics_Types.all_implicits);
                          FStar_Tactics_Types.goals = lgs;
                          FStar_Tactics_Types.smt_goals = [];
                          FStar_Tactics_Types.depth =
                            (uu___82_2102.FStar_Tactics_Types.depth);
                          FStar_Tactics_Types.__dump =
                            (uu___82_2102.FStar_Tactics_Types.__dump);
                          FStar_Tactics_Types.psc =
                            (uu___82_2102.FStar_Tactics_Types.psc);
                          FStar_Tactics_Types.entry_range =
                            (uu___82_2102.FStar_Tactics_Types.entry_range);
                          FStar_Tactics_Types.guard_policy =
                            (uu___82_2102.FStar_Tactics_Types.guard_policy)
                        }  in
                      let rp =
                        let uu___83_2104 = p  in
                        {
                          FStar_Tactics_Types.main_context =
                            (uu___83_2104.FStar_Tactics_Types.main_context);
                          FStar_Tactics_Types.main_goal =
                            (uu___83_2104.FStar_Tactics_Types.main_goal);
                          FStar_Tactics_Types.all_implicits =
                            (uu___83_2104.FStar_Tactics_Types.all_implicits);
                          FStar_Tactics_Types.goals = rgs;
                          FStar_Tactics_Types.smt_goals = [];
                          FStar_Tactics_Types.depth =
                            (uu___83_2104.FStar_Tactics_Types.depth);
                          FStar_Tactics_Types.__dump =
                            (uu___83_2104.FStar_Tactics_Types.__dump);
                          FStar_Tactics_Types.psc =
                            (uu___83_2104.FStar_Tactics_Types.psc);
                          FStar_Tactics_Types.entry_range =
                            (uu___83_2104.FStar_Tactics_Types.entry_range);
                          FStar_Tactics_Types.guard_policy =
                            (uu___83_2104.FStar_Tactics_Types.guard_policy)
                        }  in
                      let uu____2105 = set lp  in
                      bind uu____2105
                        (fun uu____2113  ->
                           bind l
                             (fun a  ->
                                bind get
                                  (fun lp'  ->
                                     let uu____2127 = set rp  in
                                     bind uu____2127
                                       (fun uu____2135  ->
                                          bind r
                                            (fun b  ->
                                               bind get
                                                 (fun rp'  ->
                                                    let p' =
                                                      let uu___84_2151 = p
                                                         in
                                                      {
                                                        FStar_Tactics_Types.main_context
                                                          =
                                                          (uu___84_2151.FStar_Tactics_Types.main_context);
                                                        FStar_Tactics_Types.main_goal
                                                          =
                                                          (uu___84_2151.FStar_Tactics_Types.main_goal);
                                                        FStar_Tactics_Types.all_implicits
                                                          =
                                                          (uu___84_2151.FStar_Tactics_Types.all_implicits);
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
                                                          (uu___84_2151.FStar_Tactics_Types.depth);
                                                        FStar_Tactics_Types.__dump
                                                          =
                                                          (uu___84_2151.FStar_Tactics_Types.__dump);
                                                        FStar_Tactics_Types.psc
                                                          =
                                                          (uu___84_2151.FStar_Tactics_Types.psc);
                                                        FStar_Tactics_Types.entry_range
                                                          =
                                                          (uu___84_2151.FStar_Tactics_Types.entry_range);
                                                        FStar_Tactics_Types.guard_policy
                                                          =
                                                          (uu___84_2151.FStar_Tactics_Types.guard_policy)
                                                      }  in
                                                    let uu____2152 = set p'
                                                       in
                                                    bind uu____2152
                                                      (fun uu____2160  ->
                                                         ret (a, b))))))))))
  
let focus : 'a . 'a tac -> 'a tac =
  fun f  ->
    let uu____2178 = divide FStar_BigInt.one f idtac  in
    bind uu____2178
      (fun uu____2191  -> match uu____2191 with | (a,()) -> ret a)
  
let rec map : 'a . 'a tac -> 'a Prims.list tac =
  fun tau  ->
    bind get
      (fun p  ->
         match p.FStar_Tactics_Types.goals with
         | [] -> ret []
         | uu____2225::uu____2226 ->
             let uu____2229 =
               let uu____2238 = map tau  in
               divide FStar_BigInt.one tau uu____2238  in
             bind uu____2229
               (fun uu____2256  ->
                  match uu____2256 with | (h,t) -> ret (h :: t)))
  
let (seq : Prims.unit tac -> Prims.unit tac -> Prims.unit tac) =
  fun t1  ->
    fun t2  ->
      let uu____2293 =
        bind t1
          (fun uu____2298  ->
             let uu____2299 = map t2  in
             bind uu____2299 (fun uu____2307  -> ret ()))
         in
      focus uu____2293
  
let (intro : FStar_Syntax_Syntax.binder tac) =
  let uu____2314 =
    bind cur_goal
      (fun goal  ->
         let uu____2323 =
           FStar_Syntax_Util.arrow_one goal.FStar_Tactics_Types.goal_ty  in
         match uu____2323 with
         | FStar_Pervasives_Native.Some (b,c) ->
             let uu____2338 =
               let uu____2339 = FStar_Syntax_Util.is_total_comp c  in
               Prims.op_Negation uu____2339  in
             if uu____2338
             then fail "Codomain is effectful"
             else
               (let env' =
                  FStar_TypeChecker_Env.push_binders
                    goal.FStar_Tactics_Types.context [b]
                   in
                let typ' = comp_to_typ c  in
                let uu____2345 = new_uvar "intro" env' typ'  in
                bind uu____2345
                  (fun u  ->
                     let uu____2351 =
                       let uu____2354 =
                         FStar_Syntax_Util.abs [b] u
                           FStar_Pervasives_Native.None
                          in
                       trysolve goal uu____2354  in
                     bind uu____2351
                       (fun bb  ->
                          if bb
                          then
                            let uu____2360 =
                              let uu____2363 =
                                let uu___87_2364 = goal  in
                                let uu____2365 = bnorm env' u  in
                                let uu____2366 = bnorm env' typ'  in
                                {
                                  FStar_Tactics_Types.context = env';
                                  FStar_Tactics_Types.witness = uu____2365;
                                  FStar_Tactics_Types.goal_ty = uu____2366;
                                  FStar_Tactics_Types.opts =
                                    (uu___87_2364.FStar_Tactics_Types.opts);
                                  FStar_Tactics_Types.is_guard =
                                    (uu___87_2364.FStar_Tactics_Types.is_guard)
                                }  in
                              replace_cur uu____2363  in
                            bind uu____2360 (fun uu____2368  -> ret b)
                          else fail "unification failed")))
         | FStar_Pervasives_Native.None  ->
             let uu____2374 =
               tts goal.FStar_Tactics_Types.context
                 goal.FStar_Tactics_Types.goal_ty
                in
             fail1 "goal is not an arrow (%s)" uu____2374)
     in
  FStar_All.pipe_left (wrap_err "intro") uu____2314 
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
       (let uu____2405 =
          FStar_Syntax_Util.arrow_one goal.FStar_Tactics_Types.goal_ty  in
        match uu____2405 with
        | FStar_Pervasives_Native.Some (b,c) ->
            let uu____2424 =
              let uu____2425 = FStar_Syntax_Util.is_total_comp c  in
              Prims.op_Negation uu____2425  in
            if uu____2424
            then fail "Codomain is effectful"
            else
              (let bv =
                 FStar_Syntax_Syntax.gen_bv "__recf"
                   FStar_Pervasives_Native.None
                   goal.FStar_Tactics_Types.goal_ty
                  in
               let bs =
                 let uu____2441 = FStar_Syntax_Syntax.mk_binder bv  in
                 [uu____2441; b]  in
               let env' =
                 FStar_TypeChecker_Env.push_binders
                   goal.FStar_Tactics_Types.context bs
                  in
               let uu____2443 =
                 let uu____2446 = comp_to_typ c  in
                 new_uvar "intro_rec" env' uu____2446  in
               bind uu____2443
                 (fun u  ->
                    let lb =
                      let uu____2461 =
                        FStar_Syntax_Util.abs [b] u
                          FStar_Pervasives_Native.None
                         in
                      FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl bv) []
                        goal.FStar_Tactics_Types.goal_ty
                        FStar_Parser_Const.effect_Tot_lid uu____2461 []
                        FStar_Range.dummyRange
                       in
                    let body = FStar_Syntax_Syntax.bv_to_name bv  in
                    let uu____2467 =
                      FStar_Syntax_Subst.close_let_rec [lb] body  in
                    match uu____2467 with
                    | (lbs,body1) ->
                        let tm =
                          FStar_Syntax_Syntax.mk
                            (FStar_Syntax_Syntax.Tm_let ((true, lbs), body1))
                            FStar_Pervasives_Native.None
                            (goal.FStar_Tactics_Types.witness).FStar_Syntax_Syntax.pos
                           in
                        let uu____2497 = trysolve goal tm  in
                        bind uu____2497
                          (fun bb  ->
                             if bb
                             then
                               let uu____2513 =
                                 let uu____2516 =
                                   let uu___88_2517 = goal  in
                                   let uu____2518 = bnorm env' u  in
                                   let uu____2519 =
                                     let uu____2520 = comp_to_typ c  in
                                     bnorm env' uu____2520  in
                                   {
                                     FStar_Tactics_Types.context = env';
                                     FStar_Tactics_Types.witness = uu____2518;
                                     FStar_Tactics_Types.goal_ty = uu____2519;
                                     FStar_Tactics_Types.opts =
                                       (uu___88_2517.FStar_Tactics_Types.opts);
                                     FStar_Tactics_Types.is_guard =
                                       (uu___88_2517.FStar_Tactics_Types.is_guard)
                                   }  in
                                 replace_cur uu____2516  in
                               bind uu____2513
                                 (fun uu____2527  ->
                                    let uu____2528 =
                                      let uu____2533 =
                                        FStar_Syntax_Syntax.mk_binder bv  in
                                      (uu____2533, b)  in
                                    ret uu____2528)
                             else fail "intro_rec: unification failed")))
        | FStar_Pervasives_Native.None  ->
            let uu____2547 =
              tts goal.FStar_Tactics_Types.context
                goal.FStar_Tactics_Types.goal_ty
               in
            fail1 "intro_rec: goal is not an arrow (%s)" uu____2547))
  
let (norm : FStar_Syntax_Embeddings.norm_step Prims.list -> Prims.unit tac) =
  fun s  ->
    bind cur_goal
      (fun goal  ->
         mlog
           (fun uu____2567  ->
              let uu____2568 =
                FStar_Syntax_Print.term_to_string
                  goal.FStar_Tactics_Types.witness
                 in
              FStar_Util.print1 "norm: witness = %s\n" uu____2568)
           (fun uu____2573  ->
              let steps =
                let uu____2577 = FStar_TypeChecker_Normalize.tr_norm_steps s
                   in
                FStar_List.append
                  [FStar_TypeChecker_Normalize.Reify;
                  FStar_TypeChecker_Normalize.UnfoldTac] uu____2577
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
                (let uu___89_2584 = goal  in
                 {
                   FStar_Tactics_Types.context =
                     (uu___89_2584.FStar_Tactics_Types.context);
                   FStar_Tactics_Types.witness = w;
                   FStar_Tactics_Types.goal_ty = t;
                   FStar_Tactics_Types.opts =
                     (uu___89_2584.FStar_Tactics_Types.opts);
                   FStar_Tactics_Types.is_guard =
                     (uu___89_2584.FStar_Tactics_Types.is_guard)
                 })))
  
let (norm_term_env :
  env ->
    FStar_Syntax_Embeddings.norm_step Prims.list ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac)
  =
  fun e  ->
    fun s  ->
      fun t  ->
        let uu____2602 =
          mlog
            (fun uu____2607  ->
               let uu____2608 = FStar_Syntax_Print.term_to_string t  in
               FStar_Util.print1 "norm_term: tm = %s\n" uu____2608)
            (fun uu____2610  ->
               bind get
                 (fun ps  ->
                    let opts =
                      match ps.FStar_Tactics_Types.goals with
                      | g::uu____2616 -> g.FStar_Tactics_Types.opts
                      | uu____2619 -> FStar_Options.peek ()  in
                    mlog
                      (fun uu____2624  ->
                         let uu____2625 =
                           tts ps.FStar_Tactics_Types.main_context t  in
                         FStar_Util.print1 "norm_term_env: t = %s\n"
                           uu____2625)
                      (fun uu____2628  ->
                         let uu____2629 = __tc e t  in
                         bind uu____2629
                           (fun uu____2650  ->
                              match uu____2650 with
                              | (t1,uu____2660,uu____2661) ->
                                  let steps =
                                    let uu____2665 =
                                      FStar_TypeChecker_Normalize.tr_norm_steps
                                        s
                                       in
                                    FStar_List.append
                                      [FStar_TypeChecker_Normalize.Reify;
                                      FStar_TypeChecker_Normalize.UnfoldTac]
                                      uu____2665
                                     in
                                  let t2 =
                                    normalize steps
                                      ps.FStar_Tactics_Types.main_context t1
                                     in
                                  ret t2))))
           in
        FStar_All.pipe_left (wrap_err "norm_term") uu____2602
  
let (refine_intro : Prims.unit tac) =
  let uu____2677 =
    bind cur_goal
      (fun g  ->
         let uu____2684 =
           FStar_TypeChecker_Rel.base_and_refinement
             g.FStar_Tactics_Types.context g.FStar_Tactics_Types.goal_ty
            in
         match uu____2684 with
         | (uu____2697,FStar_Pervasives_Native.None ) ->
             fail "not a refinement"
         | (t,FStar_Pervasives_Native.Some (bv,phi)) ->
             let g1 =
               let uu___90_2722 = g  in
               {
                 FStar_Tactics_Types.context =
                   (uu___90_2722.FStar_Tactics_Types.context);
                 FStar_Tactics_Types.witness =
                   (uu___90_2722.FStar_Tactics_Types.witness);
                 FStar_Tactics_Types.goal_ty = t;
                 FStar_Tactics_Types.opts =
                   (uu___90_2722.FStar_Tactics_Types.opts);
                 FStar_Tactics_Types.is_guard =
                   (uu___90_2722.FStar_Tactics_Types.is_guard)
               }  in
             let uu____2723 =
               let uu____2728 =
                 let uu____2733 =
                   let uu____2734 = FStar_Syntax_Syntax.mk_binder bv  in
                   [uu____2734]  in
                 FStar_Syntax_Subst.open_term uu____2733 phi  in
               match uu____2728 with
               | (bvs,phi1) ->
                   let uu____2741 =
                     let uu____2742 = FStar_List.hd bvs  in
                     FStar_Pervasives_Native.fst uu____2742  in
                   (uu____2741, phi1)
                in
             (match uu____2723 with
              | (bv1,phi1) ->
                  let uu____2755 =
                    let uu____2758 =
                      FStar_Syntax_Subst.subst
                        [FStar_Syntax_Syntax.NT
                           (bv1, (g.FStar_Tactics_Types.witness))] phi1
                       in
                    mk_irrelevant_goal "refine_intro refinement"
                      g.FStar_Tactics_Types.context uu____2758
                      g.FStar_Tactics_Types.opts
                     in
                  bind uu____2755
                    (fun g2  ->
                       bind __dismiss (fun uu____2762  -> add_goals [g1; g2]))))
     in
  FStar_All.pipe_left (wrap_err "refine_intro") uu____2677 
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
           let uu____2783 = __tc env t  in
           bind uu____2783
             (fun uu____2803  ->
                match uu____2803 with
                | (t1,typ,guard) ->
                    let uu____2815 =
                      proc_guard "__exact typing"
                        goal.FStar_Tactics_Types.context guard
                        goal.FStar_Tactics_Types.opts
                       in
                    bind uu____2815
                      (fun uu____2819  ->
                         mlog
                           (fun uu____2823  ->
                              let uu____2824 =
                                tts goal.FStar_Tactics_Types.context typ  in
                              let uu____2825 =
                                tts goal.FStar_Tactics_Types.context
                                  goal.FStar_Tactics_Types.goal_ty
                                 in
                              FStar_Util.print2 "exact: unifying %s and %s\n"
                                uu____2824 uu____2825)
                           (fun uu____2828  ->
                              let uu____2829 =
                                do_unify goal.FStar_Tactics_Types.context typ
                                  goal.FStar_Tactics_Types.goal_ty
                                 in
                              bind uu____2829
                                (fun b  ->
                                   if b
                                   then solve goal t1
                                   else
                                     (let uu____2837 =
                                        tts goal.FStar_Tactics_Types.context
                                          t1
                                         in
                                      let uu____2838 =
                                        tts goal.FStar_Tactics_Types.context
                                          typ
                                         in
                                      let uu____2839 =
                                        tts goal.FStar_Tactics_Types.context
                                          goal.FStar_Tactics_Types.goal_ty
                                         in
                                      let uu____2840 =
                                        tts goal.FStar_Tactics_Types.context
                                          goal.FStar_Tactics_Types.witness
                                         in
                                      fail4
                                        "%s : %s does not exactly solve the goal %s (witness = %s)"
                                        uu____2837 uu____2838 uu____2839
                                        uu____2840))))))
  
let (t_exact : Prims.bool -> FStar_Syntax_Syntax.term -> Prims.unit tac) =
  fun set_expected_typ1  ->
    fun tm  ->
      let uu____2851 =
        mlog
          (fun uu____2856  ->
             let uu____2857 = FStar_Syntax_Print.term_to_string tm  in
             FStar_Util.print1 "t_exact: tm = %s\n" uu____2857)
          (fun uu____2860  ->
             let uu____2861 =
               let uu____2868 = __exact_now set_expected_typ1 tm  in
               trytac' uu____2868  in
             bind uu____2861
               (fun uu___58_2877  ->
                  match uu___58_2877 with
                  | FStar_Util.Inr r -> ret ()
                  | FStar_Util.Inl e ->
                      let uu____2886 =
                        let uu____2893 =
                          let uu____2896 =
                            norm [FStar_Syntax_Embeddings.Delta]  in
                          bind uu____2896
                            (fun uu____2900  ->
                               bind refine_intro
                                 (fun uu____2902  ->
                                    __exact_now set_expected_typ1 tm))
                           in
                        trytac' uu____2893  in
                      bind uu____2886
                        (fun uu___57_2909  ->
                           match uu___57_2909 with
                           | FStar_Util.Inr r -> ret ()
                           | FStar_Util.Inl uu____2917 -> fail e)))
         in
      FStar_All.pipe_left (wrap_err "exact") uu____2851
  
let (uvar_free_in_goal :
  FStar_Syntax_Syntax.uvar -> FStar_Tactics_Types.goal -> Prims.bool) =
  fun u  ->
    fun g  ->
      if g.FStar_Tactics_Types.is_guard
      then false
      else
        (let free_uvars =
           let uu____2932 =
             let uu____2939 =
               FStar_Syntax_Free.uvars g.FStar_Tactics_Types.goal_ty  in
             FStar_Util.set_elements uu____2939  in
           FStar_List.map FStar_Pervasives_Native.fst uu____2932  in
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
          let uu____2999 = f x  in
          bind uu____2999
            (fun y  ->
               let uu____3007 = mapM f xs  in
               bind uu____3007 (fun ys  -> ret (y :: ys)))
  
exception NoUnif 
let (uu___is_NoUnif : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with | NoUnif  -> true | uu____3025 -> false
  
let rec (__apply :
  Prims.bool ->
    FStar_Syntax_Syntax.term -> FStar_Reflection_Data.typ -> Prims.unit tac)
  =
  fun uopt  ->
    fun tm  ->
      fun typ  ->
        bind cur_goal
          (fun goal  ->
             mlog
               (fun uu____3043  ->
                  let uu____3044 = FStar_Syntax_Print.term_to_string tm  in
                  FStar_Util.print1 ">>> Calling __exact(%s)\n" uu____3044)
               (fun uu____3047  ->
                  let uu____3048 =
                    let uu____3053 =
                      let uu____3056 = t_exact false tm  in
                      with_policy FStar_Tactics_Types.Force uu____3056  in
                    trytac_exn uu____3053  in
                  bind uu____3048
                    (fun uu___59_3063  ->
                       match uu___59_3063 with
                       | FStar_Pervasives_Native.Some r -> ret ()
                       | FStar_Pervasives_Native.None  ->
                           mlog
                             (fun uu____3071  ->
                                let uu____3072 =
                                  FStar_Syntax_Print.term_to_string typ  in
                                FStar_Util.print1 ">>> typ = %s\n" uu____3072)
                             (fun uu____3075  ->
                                let uu____3076 =
                                  FStar_Syntax_Util.arrow_one typ  in
                                match uu____3076 with
                                | FStar_Pervasives_Native.None  ->
                                    FStar_Exn.raise NoUnif
                                | FStar_Pervasives_Native.Some ((bv,aq),c) ->
                                    mlog
                                      (fun uu____3108  ->
                                         let uu____3109 =
                                           FStar_Syntax_Print.binder_to_string
                                             (bv, aq)
                                            in
                                         FStar_Util.print1
                                           "__apply: pushing binder %s\n"
                                           uu____3109)
                                      (fun uu____3112  ->
                                         let uu____3113 =
                                           let uu____3114 =
                                             FStar_Syntax_Util.is_total_comp
                                               c
                                              in
                                           Prims.op_Negation uu____3114  in
                                         if uu____3113
                                         then
                                           fail "apply: not total codomain"
                                         else
                                           (let uu____3118 =
                                              new_uvar "apply"
                                                goal.FStar_Tactics_Types.context
                                                bv.FStar_Syntax_Syntax.sort
                                               in
                                            bind uu____3118
                                              (fun u  ->
                                                 let tm' =
                                                   FStar_Syntax_Syntax.mk_Tm_app
                                                     tm [(u, aq)]
                                                     FStar_Pervasives_Native.None
                                                     tm.FStar_Syntax_Syntax.pos
                                                    in
                                                 let typ' =
                                                   let uu____3138 =
                                                     comp_to_typ c  in
                                                   FStar_All.pipe_left
                                                     (FStar_Syntax_Subst.subst
                                                        [FStar_Syntax_Syntax.NT
                                                           (bv, u)])
                                                     uu____3138
                                                    in
                                                 let uu____3139 =
                                                   __apply uopt tm' typ'  in
                                                 bind uu____3139
                                                   (fun uu____3147  ->
                                                      let u1 =
                                                        bnorm
                                                          goal.FStar_Tactics_Types.context
                                                          u
                                                         in
                                                      let uu____3149 =
                                                        let uu____3150 =
                                                          let uu____3153 =
                                                            let uu____3154 =
                                                              FStar_Syntax_Util.head_and_args
                                                                u1
                                                               in
                                                            FStar_Pervasives_Native.fst
                                                              uu____3154
                                                             in
                                                          FStar_Syntax_Subst.compress
                                                            uu____3153
                                                           in
                                                        uu____3150.FStar_Syntax_Syntax.n
                                                         in
                                                      match uu____3149 with
                                                      | FStar_Syntax_Syntax.Tm_uvar
                                                          (uvar,uu____3182)
                                                          ->
                                                          bind get
                                                            (fun ps  ->
                                                               let uu____3210
                                                                 =
                                                                 uopt &&
                                                                   (uvar_free
                                                                    uvar ps)
                                                                  in
                                                               if uu____3210
                                                               then ret ()
                                                               else
                                                                 (let uu____3214
                                                                    =
                                                                    let uu____3217
                                                                    =
                                                                    let uu___91_3218
                                                                    = goal
                                                                     in
                                                                    let uu____3219
                                                                    =
                                                                    bnorm
                                                                    goal.FStar_Tactics_Types.context
                                                                    u1  in
                                                                    let uu____3220
                                                                    =
                                                                    bnorm
                                                                    goal.FStar_Tactics_Types.context
                                                                    bv.FStar_Syntax_Syntax.sort
                                                                     in
                                                                    {
                                                                    FStar_Tactics_Types.context
                                                                    =
                                                                    (uu___91_3218.FStar_Tactics_Types.context);
                                                                    FStar_Tactics_Types.witness
                                                                    =
                                                                    uu____3219;
                                                                    FStar_Tactics_Types.goal_ty
                                                                    =
                                                                    uu____3220;
                                                                    FStar_Tactics_Types.opts
                                                                    =
                                                                    (uu___91_3218.FStar_Tactics_Types.opts);
                                                                    FStar_Tactics_Types.is_guard
                                                                    = false
                                                                    }  in
                                                                    [uu____3217]
                                                                     in
                                                                  add_goals
                                                                    uu____3214))
                                                      | t -> ret ()))))))))
  
let try_unif : 'a . 'a tac -> 'a tac -> 'a tac =
  fun t  ->
    fun t'  -> mk_tac (fun ps  -> try run t ps with | NoUnif  -> run t' ps)
  
let (apply : Prims.bool -> FStar_Syntax_Syntax.term -> Prims.unit tac) =
  fun uopt  ->
    fun tm  ->
      let uu____3266 =
        mlog
          (fun uu____3271  ->
             let uu____3272 = FStar_Syntax_Print.term_to_string tm  in
             FStar_Util.print1 "apply: tm = %s\n" uu____3272)
          (fun uu____3274  ->
             bind cur_goal
               (fun goal  ->
                  let uu____3278 = __tc goal.FStar_Tactics_Types.context tm
                     in
                  bind uu____3278
                    (fun uu____3300  ->
                       match uu____3300 with
                       | (tm1,typ,guard) ->
                           let typ1 =
                             bnorm goal.FStar_Tactics_Types.context typ  in
                           let uu____3313 =
                             let uu____3316 =
                               let uu____3319 = __apply uopt tm1 typ1  in
                               bind uu____3319
                                 (fun uu____3323  ->
                                    proc_guard "apply guard"
                                      goal.FStar_Tactics_Types.context guard
                                      goal.FStar_Tactics_Types.opts)
                                in
                             focus uu____3316  in
                           let uu____3324 =
                             let uu____3327 =
                               tts goal.FStar_Tactics_Types.context tm1  in
                             let uu____3328 =
                               tts goal.FStar_Tactics_Types.context typ1  in
                             let uu____3329 =
                               tts goal.FStar_Tactics_Types.context
                                 goal.FStar_Tactics_Types.goal_ty
                                in
                             fail3
                               "Cannot instantiate %s (of type %s) to match goal (%s)"
                               uu____3327 uu____3328 uu____3329
                              in
                           try_unif uu____3313 uu____3324)))
         in
      FStar_All.pipe_left (wrap_err "apply") uu____3266
  
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
      let uu____3356 =
        match ct.FStar_Syntax_Syntax.effect_args with
        | pre::post::uu____3375 ->
            ((FStar_Pervasives_Native.fst pre),
              (FStar_Pervasives_Native.fst post))
        | uu____3416 -> failwith "apply_lemma: impossible: not a lemma"  in
      match uu____3356 with
      | (pre,post) ->
          let post1 =
            let uu____3452 =
              let uu____3461 =
                FStar_Syntax_Syntax.as_arg FStar_Syntax_Util.exp_unit  in
              [uu____3461]  in
            FStar_Syntax_Util.mk_app post uu____3452  in
          FStar_Pervasives_Native.Some (pre, post1)
    else
      if FStar_Syntax_Util.is_pure_effect ct.FStar_Syntax_Syntax.effect_name
      then
        (let uu____3481 =
           FStar_Syntax_Util.un_squash ct.FStar_Syntax_Syntax.result_typ  in
         FStar_Util.map_opt uu____3481
           (fun post  -> (FStar_Syntax_Util.t_true, post)))
      else FStar_Pervasives_Native.None
  
let (apply_lemma : FStar_Syntax_Syntax.term -> Prims.unit tac) =
  fun tm  ->
    let uu____3512 =
      let uu____3515 =
        mlog
          (fun uu____3520  ->
             let uu____3521 = FStar_Syntax_Print.term_to_string tm  in
             FStar_Util.print1 "apply_lemma: tm = %s\n" uu____3521)
          (fun uu____3524  ->
             let is_unit_t t =
               let uu____3529 =
                 let uu____3530 = FStar_Syntax_Subst.compress t  in
                 uu____3530.FStar_Syntax_Syntax.n  in
               match uu____3529 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.unit_lid
                   -> true
               | uu____3534 -> false  in
             bind cur_goal
               (fun goal  ->
                  let uu____3538 = __tc goal.FStar_Tactics_Types.context tm
                     in
                  bind uu____3538
                    (fun uu____3561  ->
                       match uu____3561 with
                       | (tm1,t,guard) ->
                           let uu____3573 =
                             FStar_Syntax_Util.arrow_formals_comp t  in
                           (match uu____3573 with
                            | (bs,comp) ->
                                let uu____3600 = lemma_or_sq comp  in
                                (match uu____3600 with
                                 | FStar_Pervasives_Native.None  ->
                                     fail "not a lemma or squashed function"
                                 | FStar_Pervasives_Native.Some (pre,post) ->
                                     let uu____3619 =
                                       FStar_List.fold_left
                                         (fun uu____3665  ->
                                            fun uu____3666  ->
                                              match (uu____3665, uu____3666)
                                              with
                                              | ((uvs,guard1,subst1),(b,aq))
                                                  ->
                                                  let b_t =
                                                    FStar_Syntax_Subst.subst
                                                      subst1
                                                      b.FStar_Syntax_Syntax.sort
                                                     in
                                                  let uu____3769 =
                                                    is_unit_t b_t  in
                                                  if uu____3769
                                                  then
                                                    (((FStar_Syntax_Util.exp_unit,
                                                        aq) :: uvs), guard1,
                                                      ((FStar_Syntax_Syntax.NT
                                                          (b,
                                                            FStar_Syntax_Util.exp_unit))
                                                      :: subst1))
                                                  else
                                                    (let uu____3807 =
                                                       FStar_TypeChecker_Util.new_implicit_var
                                                         "apply_lemma"
                                                         (goal.FStar_Tactics_Types.goal_ty).FStar_Syntax_Syntax.pos
                                                         goal.FStar_Tactics_Types.context
                                                         b_t
                                                        in
                                                     match uu____3807 with
                                                     | (u,uu____3837,g_u) ->
                                                         let uu____3851 =
                                                           FStar_TypeChecker_Rel.conj_guard
                                                             guard1 g_u
                                                            in
                                                         (((u, aq) :: uvs),
                                                           uu____3851,
                                                           ((FStar_Syntax_Syntax.NT
                                                               (b, u)) ::
                                                           subst1))))
                                         ([], guard, []) bs
                                        in
                                     (match uu____3619 with
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
                                          let uu____3922 =
                                            let uu____3925 =
                                              FStar_Syntax_Util.mk_squash
                                                FStar_Syntax_Syntax.U_zero
                                                post1
                                               in
                                            do_unify
                                              goal.FStar_Tactics_Types.context
                                              uu____3925
                                              goal.FStar_Tactics_Types.goal_ty
                                             in
                                          bind uu____3922
                                            (fun b  ->
                                               if Prims.op_Negation b
                                               then
                                                 let uu____3933 =
                                                   tts
                                                     goal.FStar_Tactics_Types.context
                                                     tm1
                                                    in
                                                 let uu____3934 =
                                                   let uu____3935 =
                                                     FStar_Syntax_Util.mk_squash
                                                       FStar_Syntax_Syntax.U_zero
                                                       post1
                                                      in
                                                   tts
                                                     goal.FStar_Tactics_Types.context
                                                     uu____3935
                                                    in
                                                 let uu____3936 =
                                                   tts
                                                     goal.FStar_Tactics_Types.context
                                                     goal.FStar_Tactics_Types.goal_ty
                                                    in
                                                 fail3
                                                   "Cannot instantiate lemma %s (with postcondition: %s) to match goal (%s)"
                                                   uu____3933 uu____3934
                                                   uu____3936
                                               else
                                                 (let uu____3938 =
                                                    add_implicits
                                                      implicits.FStar_TypeChecker_Env.implicits
                                                     in
                                                  bind uu____3938
                                                    (fun uu____3943  ->
                                                       let uu____3944 =
                                                         solve goal
                                                           FStar_Syntax_Util.exp_unit
                                                          in
                                                       bind uu____3944
                                                         (fun uu____3952  ->
                                                            let is_free_uvar
                                                              uv t1 =
                                                              let free_uvars
                                                                =
                                                                let uu____3963
                                                                  =
                                                                  let uu____3970
                                                                    =
                                                                    FStar_Syntax_Free.uvars
                                                                    t1  in
                                                                  FStar_Util.set_elements
                                                                    uu____3970
                                                                   in
                                                                FStar_List.map
                                                                  FStar_Pervasives_Native.fst
                                                                  uu____3963
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
                                                              let uu____4011
                                                                =
                                                                FStar_Syntax_Util.head_and_args
                                                                  t1
                                                                 in
                                                              match uu____4011
                                                              with
                                                              | (hd1,uu____4027)
                                                                  ->
                                                                  (match 
                                                                    hd1.FStar_Syntax_Syntax.n
                                                                   with
                                                                   | 
                                                                   FStar_Syntax_Syntax.Tm_uvar
                                                                    (uv,uu____4049)
                                                                    ->
                                                                    appears
                                                                    uv goals
                                                                   | 
                                                                   uu____4074
                                                                    -> false)
                                                               in
                                                            let uu____4075 =
                                                              FStar_All.pipe_right
                                                                implicits.FStar_TypeChecker_Env.implicits
                                                                (mapM
                                                                   (fun
                                                                    uu____4147
                                                                     ->
                                                                    match uu____4147
                                                                    with
                                                                    | 
                                                                    (_msg,env,_uvar,term,typ,uu____4175)
                                                                    ->
                                                                    let uu____4176
                                                                    =
                                                                    FStar_Syntax_Util.head_and_args
                                                                    term  in
                                                                    (match uu____4176
                                                                    with
                                                                    | 
                                                                    (hd1,uu____4202)
                                                                    ->
                                                                    let uu____4223
                                                                    =
                                                                    let uu____4224
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    hd1  in
                                                                    uu____4224.FStar_Syntax_Syntax.n
                                                                     in
                                                                    (match uu____4223
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Tm_uvar
                                                                    uu____4237
                                                                    ->
                                                                    let uu____4254
                                                                    =
                                                                    let uu____4263
                                                                    =
                                                                    let uu____4266
                                                                    =
                                                                    let uu___94_4267
                                                                    = goal
                                                                     in
                                                                    let uu____4268
                                                                    =
                                                                    bnorm
                                                                    goal.FStar_Tactics_Types.context
                                                                    term  in
                                                                    let uu____4269
                                                                    =
                                                                    bnorm
                                                                    goal.FStar_Tactics_Types.context
                                                                    typ  in
                                                                    {
                                                                    FStar_Tactics_Types.context
                                                                    =
                                                                    (uu___94_4267.FStar_Tactics_Types.context);
                                                                    FStar_Tactics_Types.witness
                                                                    =
                                                                    uu____4268;
                                                                    FStar_Tactics_Types.goal_ty
                                                                    =
                                                                    uu____4269;
                                                                    FStar_Tactics_Types.opts
                                                                    =
                                                                    (uu___94_4267.FStar_Tactics_Types.opts);
                                                                    FStar_Tactics_Types.is_guard
                                                                    =
                                                                    (uu___94_4267.FStar_Tactics_Types.is_guard)
                                                                    }  in
                                                                    [uu____4266]
                                                                     in
                                                                    (uu____4263,
                                                                    [])  in
                                                                    ret
                                                                    uu____4254
                                                                    | 
                                                                    uu____4282
                                                                    ->
                                                                    let g_typ
                                                                    =
                                                                    let uu____4284
                                                                    =
                                                                    FStar_Options.__temp_fast_implicits
                                                                    ()  in
                                                                    if
                                                                    uu____4284
                                                                    then
                                                                    FStar_TypeChecker_TcTerm.check_type_of_well_typed_term
                                                                    false env
                                                                    term typ
                                                                    else
                                                                    (let term1
                                                                    =
                                                                    bnorm env
                                                                    term  in
                                                                    let uu____4287
                                                                    =
                                                                    let uu____4294
                                                                    =
                                                                    FStar_TypeChecker_Env.set_expected_typ
                                                                    env typ
                                                                     in
                                                                    env.FStar_TypeChecker_Env.type_of
                                                                    uu____4294
                                                                    term1  in
                                                                    match uu____4287
                                                                    with
                                                                    | 
                                                                    (uu____4295,uu____4296,g_typ)
                                                                    -> g_typ)
                                                                     in
                                                                    let uu____4298
                                                                    =
                                                                    goal_from_guard
                                                                    "apply_lemma solved arg"
                                                                    goal.FStar_Tactics_Types.context
                                                                    g_typ
                                                                    goal.FStar_Tactics_Types.opts
                                                                     in
                                                                    bind
                                                                    uu____4298
                                                                    (fun
                                                                    uu___60_4314
                                                                     ->
                                                                    match uu___60_4314
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
                                                            bind uu____4075
                                                              (fun goals_  ->
                                                                 let sub_goals
                                                                   =
                                                                   let uu____4382
                                                                    =
                                                                    FStar_List.map
                                                                    FStar_Pervasives_Native.fst
                                                                    goals_
                                                                     in
                                                                   FStar_List.flatten
                                                                    uu____4382
                                                                    in
                                                                 let smt_goals
                                                                   =
                                                                   let uu____4404
                                                                    =
                                                                    FStar_List.map
                                                                    FStar_Pervasives_Native.snd
                                                                    goals_
                                                                     in
                                                                   FStar_List.flatten
                                                                    uu____4404
                                                                    in
                                                                 let rec filter'
                                                                   a f xs =
                                                                   match xs
                                                                   with
                                                                   | 
                                                                   [] -> []
                                                                   | 
                                                                   x::xs1 ->
                                                                    let uu____4459
                                                                    = f x xs1
                                                                     in
                                                                    if
                                                                    uu____4459
                                                                    then
                                                                    let uu____4462
                                                                    =
                                                                    filter'
                                                                    () f xs1
                                                                     in x ::
                                                                    uu____4462
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
                                                                    let uu____4476
                                                                    =
                                                                    checkone
                                                                    g.FStar_Tactics_Types.witness
                                                                    goals  in
                                                                    Prims.op_Negation
                                                                    uu____4476))
                                                                    a438 a439)
                                                                    (Obj.magic
                                                                    sub_goals))
                                                                    in
                                                                 let uu____4477
                                                                   =
                                                                   proc_guard
                                                                    "apply_lemma guard"
                                                                    goal.FStar_Tactics_Types.context
                                                                    guard
                                                                    goal.FStar_Tactics_Types.opts
                                                                    in
                                                                 bind
                                                                   uu____4477
                                                                   (fun
                                                                    uu____4482
                                                                     ->
                                                                    let uu____4483
                                                                    =
                                                                    let uu____4486
                                                                    =
                                                                    let uu____4487
                                                                    =
                                                                    let uu____4488
                                                                    =
                                                                    FStar_Syntax_Util.mk_squash
                                                                    FStar_Syntax_Syntax.U_zero
                                                                    pre1  in
                                                                    istrivial
                                                                    goal.FStar_Tactics_Types.context
                                                                    uu____4488
                                                                     in
                                                                    Prims.op_Negation
                                                                    uu____4487
                                                                     in
                                                                    if
                                                                    uu____4486
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
                                                                    uu____4483
                                                                    (fun
                                                                    uu____4494
                                                                     ->
                                                                    let uu____4495
                                                                    =
                                                                    add_smt_goals
                                                                    smt_goals
                                                                     in
                                                                    bind
                                                                    uu____4495
                                                                    (fun
                                                                    uu____4499
                                                                     ->
                                                                    add_goals
                                                                    sub_goals1))))))))))))))
         in
      focus uu____3515  in
    FStar_All.pipe_left (wrap_err "apply_lemma") uu____3512
  
let (destruct_eq' :
  FStar_Reflection_Data.typ ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun typ  ->
    let uu____4519 = FStar_Syntax_Util.destruct_typ_as_formula typ  in
    match uu____4519 with
    | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn
        (l,uu____4529::(e1,uu____4531)::(e2,uu____4533)::[])) when
        FStar_Ident.lid_equals l FStar_Parser_Const.eq2_lid ->
        FStar_Pervasives_Native.Some (e1, e2)
    | uu____4592 -> FStar_Pervasives_Native.None
  
let (destruct_eq :
  FStar_Reflection_Data.typ ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun typ  ->
    let uu____4614 = destruct_eq' typ  in
    match uu____4614 with
    | FStar_Pervasives_Native.Some t -> FStar_Pervasives_Native.Some t
    | FStar_Pervasives_Native.None  ->
        let uu____4644 = FStar_Syntax_Util.un_squash typ  in
        (match uu____4644 with
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
        let uu____4700 = FStar_TypeChecker_Env.pop_bv e1  in
        match uu____4700 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (bv',e') ->
            if FStar_Syntax_Syntax.bv_eq bvar bv'
            then FStar_Pervasives_Native.Some (e', [])
            else
              (let uu____4748 = aux e'  in
               FStar_Util.map_opt uu____4748
                 (fun uu____4772  ->
                    match uu____4772 with | (e'',bvs) -> (e'', (bv' :: bvs))))
         in
      let uu____4793 = aux e  in
      FStar_Util.map_opt uu____4793
        (fun uu____4817  ->
           match uu____4817 with | (e',bvs) -> (e', (FStar_List.rev bvs)))
  
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
          let uu____4872 = split_env b1 g.FStar_Tactics_Types.context  in
          FStar_Util.map_opt uu____4872
            (fun uu____4896  ->
               match uu____4896 with
               | (e0,bvs) ->
                   let s1 bv =
                     let uu___95_4913 = bv  in
                     let uu____4914 =
                       FStar_Syntax_Subst.subst s bv.FStar_Syntax_Syntax.sort
                        in
                     {
                       FStar_Syntax_Syntax.ppname =
                         (uu___95_4913.FStar_Syntax_Syntax.ppname);
                       FStar_Syntax_Syntax.index =
                         (uu___95_4913.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort = uu____4914
                     }  in
                   let bvs1 = FStar_List.map s1 bvs  in
                   let c = push_bvs e0 (b2 :: bvs1)  in
                   let w =
                     FStar_Syntax_Subst.subst s g.FStar_Tactics_Types.witness
                      in
                   let t =
                     FStar_Syntax_Subst.subst s g.FStar_Tactics_Types.goal_ty
                      in
                   let uu___96_4923 = g  in
                   {
                     FStar_Tactics_Types.context = c;
                     FStar_Tactics_Types.witness = w;
                     FStar_Tactics_Types.goal_ty = t;
                     FStar_Tactics_Types.opts =
                       (uu___96_4923.FStar_Tactics_Types.opts);
                     FStar_Tactics_Types.is_guard =
                       (uu___96_4923.FStar_Tactics_Types.is_guard)
                   })
  
let (rewrite : FStar_Syntax_Syntax.binder -> Prims.unit tac) =
  fun h  ->
    bind cur_goal
      (fun goal  ->
         let uu____4936 = h  in
         match uu____4936 with
         | (bv,uu____4940) ->
             mlog
               (fun uu____4944  ->
                  let uu____4945 = FStar_Syntax_Print.bv_to_string bv  in
                  let uu____4946 =
                    tts goal.FStar_Tactics_Types.context
                      bv.FStar_Syntax_Syntax.sort
                     in
                  FStar_Util.print2 "+++Rewrite %s : %s\n" uu____4945
                    uu____4946)
               (fun uu____4949  ->
                  let uu____4950 =
                    split_env bv goal.FStar_Tactics_Types.context  in
                  match uu____4950 with
                  | FStar_Pervasives_Native.None  ->
                      fail "rewrite: binder not found in environment"
                  | FStar_Pervasives_Native.Some (e0,bvs) ->
                      let uu____4979 =
                        destruct_eq bv.FStar_Syntax_Syntax.sort  in
                      (match uu____4979 with
                       | FStar_Pervasives_Native.Some (x,e) ->
                           let uu____4994 =
                             let uu____4995 = FStar_Syntax_Subst.compress x
                                in
                             uu____4995.FStar_Syntax_Syntax.n  in
                           (match uu____4994 with
                            | FStar_Syntax_Syntax.Tm_name x1 ->
                                let s = [FStar_Syntax_Syntax.NT (x1, e)]  in
                                let s1 bv1 =
                                  let uu___97_5008 = bv1  in
                                  let uu____5009 =
                                    FStar_Syntax_Subst.subst s
                                      bv1.FStar_Syntax_Syntax.sort
                                     in
                                  {
                                    FStar_Syntax_Syntax.ppname =
                                      (uu___97_5008.FStar_Syntax_Syntax.ppname);
                                    FStar_Syntax_Syntax.index =
                                      (uu___97_5008.FStar_Syntax_Syntax.index);
                                    FStar_Syntax_Syntax.sort = uu____5009
                                  }  in
                                let bvs1 = FStar_List.map s1 bvs  in
                                let uu____5015 =
                                  let uu___98_5016 = goal  in
                                  let uu____5017 = push_bvs e0 (bv :: bvs1)
                                     in
                                  let uu____5018 =
                                    FStar_Syntax_Subst.subst s
                                      goal.FStar_Tactics_Types.witness
                                     in
                                  let uu____5019 =
                                    FStar_Syntax_Subst.subst s
                                      goal.FStar_Tactics_Types.goal_ty
                                     in
                                  {
                                    FStar_Tactics_Types.context = uu____5017;
                                    FStar_Tactics_Types.witness = uu____5018;
                                    FStar_Tactics_Types.goal_ty = uu____5019;
                                    FStar_Tactics_Types.opts =
                                      (uu___98_5016.FStar_Tactics_Types.opts);
                                    FStar_Tactics_Types.is_guard =
                                      (uu___98_5016.FStar_Tactics_Types.is_guard)
                                  }  in
                                replace_cur uu____5015
                            | uu____5020 ->
                                fail
                                  "rewrite: Not an equality hypothesis with a variable on the LHS")
                       | uu____5021 ->
                           fail "rewrite: Not an equality hypothesis")))
  
let (rename_to :
  FStar_Syntax_Syntax.binder -> Prims.string -> Prims.unit tac) =
  fun b  ->
    fun s  ->
      bind cur_goal
        (fun goal  ->
           let uu____5046 = b  in
           match uu____5046 with
           | (bv,uu____5050) ->
               let bv' =
                 FStar_Syntax_Syntax.freshen_bv
                   (let uu___99_5054 = bv  in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (FStar_Ident.mk_ident
                           (s,
                             ((bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange)));
                      FStar_Syntax_Syntax.index =
                        (uu___99_5054.FStar_Syntax_Syntax.index);
                      FStar_Syntax_Syntax.sort =
                        (uu___99_5054.FStar_Syntax_Syntax.sort)
                    })
                  in
               let s1 =
                 let uu____5058 =
                   let uu____5059 =
                     let uu____5066 = FStar_Syntax_Syntax.bv_to_name bv'  in
                     (bv, uu____5066)  in
                   FStar_Syntax_Syntax.NT uu____5059  in
                 [uu____5058]  in
               let uu____5067 = subst_goal bv bv' s1 goal  in
               (match uu____5067 with
                | FStar_Pervasives_Native.None  ->
                    fail "rename_to: binder not found in environment"
                | FStar_Pervasives_Native.Some goal1 -> replace_cur goal1))
  
let (binder_retype : FStar_Syntax_Syntax.binder -> Prims.unit tac) =
  fun b  ->
    bind cur_goal
      (fun goal  ->
         let uu____5086 = b  in
         match uu____5086 with
         | (bv,uu____5090) ->
             let uu____5091 = split_env bv goal.FStar_Tactics_Types.context
                in
             (match uu____5091 with
              | FStar_Pervasives_Native.None  ->
                  fail "binder_retype: binder is not present in environment"
              | FStar_Pervasives_Native.Some (e0,bvs) ->
                  let uu____5120 = FStar_Syntax_Util.type_u ()  in
                  (match uu____5120 with
                   | (ty,u) ->
                       let uu____5129 = new_uvar "binder_retype" e0 ty  in
                       bind uu____5129
                         (fun t'  ->
                            let bv'' =
                              let uu___100_5139 = bv  in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___100_5139.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___100_5139.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = t'
                              }  in
                            let s =
                              let uu____5143 =
                                let uu____5144 =
                                  let uu____5151 =
                                    FStar_Syntax_Syntax.bv_to_name bv''  in
                                  (bv, uu____5151)  in
                                FStar_Syntax_Syntax.NT uu____5144  in
                              [uu____5143]  in
                            let bvs1 =
                              FStar_List.map
                                (fun b1  ->
                                   let uu___101_5159 = b1  in
                                   let uu____5160 =
                                     FStar_Syntax_Subst.subst s
                                       b1.FStar_Syntax_Syntax.sort
                                      in
                                   {
                                     FStar_Syntax_Syntax.ppname =
                                       (uu___101_5159.FStar_Syntax_Syntax.ppname);
                                     FStar_Syntax_Syntax.index =
                                       (uu___101_5159.FStar_Syntax_Syntax.index);
                                     FStar_Syntax_Syntax.sort = uu____5160
                                   }) bvs
                               in
                            let env' = push_bvs e0 (bv'' :: bvs1)  in
                            bind __dismiss
                              (fun uu____5166  ->
                                 let uu____5167 =
                                   let uu____5170 =
                                     let uu____5173 =
                                       let uu___102_5174 = goal  in
                                       let uu____5175 =
                                         FStar_Syntax_Subst.subst s
                                           goal.FStar_Tactics_Types.witness
                                          in
                                       let uu____5176 =
                                         FStar_Syntax_Subst.subst s
                                           goal.FStar_Tactics_Types.goal_ty
                                          in
                                       {
                                         FStar_Tactics_Types.context = env';
                                         FStar_Tactics_Types.witness =
                                           uu____5175;
                                         FStar_Tactics_Types.goal_ty =
                                           uu____5176;
                                         FStar_Tactics_Types.opts =
                                           (uu___102_5174.FStar_Tactics_Types.opts);
                                         FStar_Tactics_Types.is_guard =
                                           (uu___102_5174.FStar_Tactics_Types.is_guard)
                                       }  in
                                     [uu____5173]  in
                                   add_goals uu____5170  in
                                 bind uu____5167
                                   (fun uu____5179  ->
                                      let uu____5180 =
                                        FStar_Syntax_Util.mk_eq2
                                          (FStar_Syntax_Syntax.U_succ u) ty
                                          bv.FStar_Syntax_Syntax.sort t'
                                         in
                                      add_irrelevant_goal
                                        "binder_retype equation" e0
                                        uu____5180
                                        goal.FStar_Tactics_Types.opts))))))
  
let (norm_binder_type :
  FStar_Syntax_Embeddings.norm_step Prims.list ->
    FStar_Syntax_Syntax.binder -> Prims.unit tac)
  =
  fun s  ->
    fun b  ->
      bind cur_goal
        (fun goal  ->
           let uu____5201 = b  in
           match uu____5201 with
           | (bv,uu____5205) ->
               let uu____5206 = split_env bv goal.FStar_Tactics_Types.context
                  in
               (match uu____5206 with
                | FStar_Pervasives_Native.None  ->
                    fail
                      "binder_retype: binder is not present in environment"
                | FStar_Pervasives_Native.Some (e0,bvs) ->
                    let steps =
                      let uu____5238 =
                        FStar_TypeChecker_Normalize.tr_norm_steps s  in
                      FStar_List.append
                        [FStar_TypeChecker_Normalize.Reify;
                        FStar_TypeChecker_Normalize.UnfoldTac] uu____5238
                       in
                    let sort' =
                      normalize steps e0 bv.FStar_Syntax_Syntax.sort  in
                    let bv' =
                      let uu___103_5243 = bv  in
                      {
                        FStar_Syntax_Syntax.ppname =
                          (uu___103_5243.FStar_Syntax_Syntax.ppname);
                        FStar_Syntax_Syntax.index =
                          (uu___103_5243.FStar_Syntax_Syntax.index);
                        FStar_Syntax_Syntax.sort = sort'
                      }  in
                    let env' = push_bvs e0 (bv' :: bvs)  in
                    replace_cur
                      (let uu___104_5247 = goal  in
                       {
                         FStar_Tactics_Types.context = env';
                         FStar_Tactics_Types.witness =
                           (uu___104_5247.FStar_Tactics_Types.witness);
                         FStar_Tactics_Types.goal_ty =
                           (uu___104_5247.FStar_Tactics_Types.goal_ty);
                         FStar_Tactics_Types.opts =
                           (uu___104_5247.FStar_Tactics_Types.opts);
                         FStar_Tactics_Types.is_guard =
                           (uu___104_5247.FStar_Tactics_Types.is_guard)
                       })))
  
let (revert : Prims.unit tac) =
  bind cur_goal
    (fun goal  ->
       let uu____5255 =
         FStar_TypeChecker_Env.pop_bv goal.FStar_Tactics_Types.context  in
       match uu____5255 with
       | FStar_Pervasives_Native.None  -> fail "Cannot revert; empty context"
       | FStar_Pervasives_Native.Some (x,env') ->
           let typ' =
             let uu____5277 =
               FStar_Syntax_Syntax.mk_Total goal.FStar_Tactics_Types.goal_ty
                in
             FStar_Syntax_Util.arrow [(x, FStar_Pervasives_Native.None)]
               uu____5277
              in
           let w' =
             FStar_Syntax_Util.abs [(x, FStar_Pervasives_Native.None)]
               goal.FStar_Tactics_Types.witness FStar_Pervasives_Native.None
              in
           replace_cur
             (let uu___105_5311 = goal  in
              {
                FStar_Tactics_Types.context = env';
                FStar_Tactics_Types.witness = w';
                FStar_Tactics_Types.goal_ty = typ';
                FStar_Tactics_Types.opts =
                  (uu___105_5311.FStar_Tactics_Types.opts);
                FStar_Tactics_Types.is_guard =
                  (uu___105_5311.FStar_Tactics_Types.is_guard)
              }))
  
let (free_in :
  FStar_Syntax_Syntax.bv -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun bv  ->
    fun t  ->
      let uu____5318 = FStar_Syntax_Free.names t  in
      FStar_Util.set_mem bv uu____5318
  
let rec (clear : FStar_Syntax_Syntax.binder -> Prims.unit tac) =
  fun b  ->
    let bv = FStar_Pervasives_Native.fst b  in
    bind cur_goal
      (fun goal  ->
         mlog
           (fun uu____5334  ->
              let uu____5335 = FStar_Syntax_Print.binder_to_string b  in
              let uu____5336 =
                let uu____5337 =
                  let uu____5338 =
                    FStar_TypeChecker_Env.all_binders
                      goal.FStar_Tactics_Types.context
                     in
                  FStar_All.pipe_right uu____5338 FStar_List.length  in
                FStar_All.pipe_right uu____5337 FStar_Util.string_of_int  in
              FStar_Util.print2 "Clear of (%s), env has %s binders\n"
                uu____5335 uu____5336)
           (fun uu____5349  ->
              let uu____5350 = split_env bv goal.FStar_Tactics_Types.context
                 in
              match uu____5350 with
              | FStar_Pervasives_Native.None  ->
                  fail "Cannot clear; binder not in environment"
              | FStar_Pervasives_Native.Some (e',bvs) ->
                  let rec check1 bvs1 =
                    match bvs1 with
                    | [] -> ret ()
                    | bv'::bvs2 ->
                        let uu____5395 =
                          free_in bv bv'.FStar_Syntax_Syntax.sort  in
                        if uu____5395
                        then
                          let uu____5398 =
                            let uu____5399 =
                              FStar_Syntax_Print.bv_to_string bv'  in
                            FStar_Util.format1
                              "Cannot clear; binder present in the type of %s"
                              uu____5399
                             in
                          fail uu____5398
                        else check1 bvs2
                     in
                  let uu____5401 =
                    free_in bv goal.FStar_Tactics_Types.goal_ty  in
                  if uu____5401
                  then fail "Cannot clear; binder present in goal"
                  else
                    (let uu____5405 = check1 bvs  in
                     bind uu____5405
                       (fun uu____5411  ->
                          let env' = push_bvs e' bvs  in
                          let uu____5413 =
                            new_uvar "clear.witness" env'
                              goal.FStar_Tactics_Types.goal_ty
                             in
                          bind uu____5413
                            (fun ut  ->
                               let uu____5419 =
                                 do_unify goal.FStar_Tactics_Types.context
                                   goal.FStar_Tactics_Types.witness ut
                                  in
                               bind uu____5419
                                 (fun b1  ->
                                    if b1
                                    then
                                      replace_cur
                                        (let uu___106_5428 = goal  in
                                         {
                                           FStar_Tactics_Types.context = env';
                                           FStar_Tactics_Types.witness = ut;
                                           FStar_Tactics_Types.goal_ty =
                                             (uu___106_5428.FStar_Tactics_Types.goal_ty);
                                           FStar_Tactics_Types.opts =
                                             (uu___106_5428.FStar_Tactics_Types.opts);
                                           FStar_Tactics_Types.is_guard =
                                             (uu___106_5428.FStar_Tactics_Types.is_guard)
                                         })
                                    else
                                      fail
                                        "Cannot clear; binder appears in witness"))))))
  
let (clear_top : Prims.unit tac) =
  bind cur_goal
    (fun goal  ->
       let uu____5437 =
         FStar_TypeChecker_Env.pop_bv goal.FStar_Tactics_Types.context  in
       match uu____5437 with
       | FStar_Pervasives_Native.None  -> fail "Cannot clear; empty context"
       | FStar_Pervasives_Native.Some (x,uu____5451) ->
           let uu____5456 = FStar_Syntax_Syntax.mk_binder x  in
           clear uu____5456)
  
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
           let uu___107_5472 = g  in
           {
             FStar_Tactics_Types.context = ctx';
             FStar_Tactics_Types.witness =
               (uu___107_5472.FStar_Tactics_Types.witness);
             FStar_Tactics_Types.goal_ty =
               (uu___107_5472.FStar_Tactics_Types.goal_ty);
             FStar_Tactics_Types.opts =
               (uu___107_5472.FStar_Tactics_Types.opts);
             FStar_Tactics_Types.is_guard =
               (uu___107_5472.FStar_Tactics_Types.is_guard)
           }  in
         bind __dismiss (fun uu____5474  -> add_goals [g']))
  
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
           let uu___108_5490 = g  in
           {
             FStar_Tactics_Types.context = ctx';
             FStar_Tactics_Types.witness =
               (uu___108_5490.FStar_Tactics_Types.witness);
             FStar_Tactics_Types.goal_ty =
               (uu___108_5490.FStar_Tactics_Types.goal_ty);
             FStar_Tactics_Types.opts =
               (uu___108_5490.FStar_Tactics_Types.opts);
             FStar_Tactics_Types.is_guard =
               (uu___108_5490.FStar_Tactics_Types.is_guard)
           }  in
         bind __dismiss (fun uu____5492  -> add_goals [g']))
  
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
            let uu____5524 = FStar_Syntax_Subst.compress t  in
            uu____5524.FStar_Syntax_Syntax.n  in
          let uu____5527 =
            if d = FStar_Tactics_Types.TopDown
            then
              f env
                (let uu___112_5533 = t  in
                 {
                   FStar_Syntax_Syntax.n = tn;
                   FStar_Syntax_Syntax.pos =
                     (uu___112_5533.FStar_Syntax_Syntax.pos);
                   FStar_Syntax_Syntax.vars =
                     (uu___112_5533.FStar_Syntax_Syntax.vars)
                 })
            else ret t  in
          bind uu____5527
            (fun t1  ->
               let ff = tac_fold_env d f env  in
               let tn1 =
                 let uu____5547 =
                   let uu____5548 = FStar_Syntax_Subst.compress t1  in
                   uu____5548.FStar_Syntax_Syntax.n  in
                 match uu____5547 with
                 | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
                     let uu____5575 = ff hd1  in
                     bind uu____5575
                       (fun hd2  ->
                          let fa uu____5595 =
                            match uu____5595 with
                            | (a,q) ->
                                let uu____5608 = ff a  in
                                bind uu____5608 (fun a1  -> ret (a1, q))
                             in
                          let uu____5621 = mapM fa args  in
                          bind uu____5621
                            (fun args1  ->
                               ret (FStar_Syntax_Syntax.Tm_app (hd2, args1))))
                 | FStar_Syntax_Syntax.Tm_abs (bs,t2,k) ->
                     let uu____5681 = FStar_Syntax_Subst.open_term bs t2  in
                     (match uu____5681 with
                      | (bs1,t') ->
                          let uu____5690 =
                            let uu____5693 =
                              FStar_TypeChecker_Env.push_binders env bs1  in
                            tac_fold_env d f uu____5693 t'  in
                          bind uu____5690
                            (fun t''  ->
                               let uu____5697 =
                                 let uu____5698 =
                                   let uu____5715 =
                                     FStar_Syntax_Subst.close_binders bs1  in
                                   let uu____5716 =
                                     FStar_Syntax_Subst.close bs1 t''  in
                                   (uu____5715, uu____5716, k)  in
                                 FStar_Syntax_Syntax.Tm_abs uu____5698  in
                               ret uu____5697))
                 | FStar_Syntax_Syntax.Tm_arrow (bs,k) -> ret tn
                 | FStar_Syntax_Syntax.Tm_match (hd1,brs) ->
                     let uu____5775 = ff hd1  in
                     bind uu____5775
                       (fun hd2  ->
                          let ffb br =
                            let uu____5788 =
                              FStar_Syntax_Subst.open_branch br  in
                            match uu____5788 with
                            | (pat,w,e) ->
                                let uu____5810 = ff e  in
                                bind uu____5810
                                  (fun e1  ->
                                     let br1 =
                                       FStar_Syntax_Subst.close_branch
                                         (pat, w, e1)
                                        in
                                     ret br1)
                             in
                          let uu____5823 = mapM ffb brs  in
                          bind uu____5823
                            (fun brs1  ->
                               ret (FStar_Syntax_Syntax.Tm_match (hd2, brs1))))
                 | FStar_Syntax_Syntax.Tm_let
                     ((false
                       ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl bv;
                          FStar_Syntax_Syntax.lbunivs = uu____5837;
                          FStar_Syntax_Syntax.lbtyp = uu____5838;
                          FStar_Syntax_Syntax.lbeff = uu____5839;
                          FStar_Syntax_Syntax.lbdef = def;
                          FStar_Syntax_Syntax.lbattrs = uu____5841;
                          FStar_Syntax_Syntax.lbpos = uu____5842;_}::[]),e)
                     ->
                     let lb =
                       let uu____5867 =
                         let uu____5868 = FStar_Syntax_Subst.compress t1  in
                         uu____5868.FStar_Syntax_Syntax.n  in
                       match uu____5867 with
                       | FStar_Syntax_Syntax.Tm_let
                           ((false ,lb::[]),uu____5872) -> lb
                       | uu____5885 -> failwith "impossible"  in
                     let fflb lb1 =
                       let uu____5892 = ff lb1.FStar_Syntax_Syntax.lbdef  in
                       bind uu____5892
                         (fun def1  ->
                            ret
                              (let uu___109_5898 = lb1  in
                               {
                                 FStar_Syntax_Syntax.lbname =
                                   (uu___109_5898.FStar_Syntax_Syntax.lbname);
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___109_5898.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp =
                                   (uu___109_5898.FStar_Syntax_Syntax.lbtyp);
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___109_5898.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def1;
                                 FStar_Syntax_Syntax.lbattrs =
                                   (uu___109_5898.FStar_Syntax_Syntax.lbattrs);
                                 FStar_Syntax_Syntax.lbpos =
                                   (uu___109_5898.FStar_Syntax_Syntax.lbpos)
                               }))
                        in
                     let uu____5899 = fflb lb  in
                     bind uu____5899
                       (fun lb1  ->
                          let uu____5908 =
                            let uu____5913 =
                              let uu____5914 =
                                FStar_Syntax_Syntax.mk_binder bv  in
                              [uu____5914]  in
                            FStar_Syntax_Subst.open_term uu____5913 e  in
                          match uu____5908 with
                          | (bs,e1) ->
                              let uu____5919 = ff e1  in
                              bind uu____5919
                                (fun e2  ->
                                   let e3 = FStar_Syntax_Subst.close bs e2
                                      in
                                   ret
                                     (FStar_Syntax_Syntax.Tm_let
                                        ((false, [lb1]), e3))))
                 | FStar_Syntax_Syntax.Tm_let ((true ,lbs),e) ->
                     let fflb lb =
                       let uu____5956 = ff lb.FStar_Syntax_Syntax.lbdef  in
                       bind uu____5956
                         (fun def  ->
                            ret
                              (let uu___110_5962 = lb  in
                               {
                                 FStar_Syntax_Syntax.lbname =
                                   (uu___110_5962.FStar_Syntax_Syntax.lbname);
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___110_5962.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp =
                                   (uu___110_5962.FStar_Syntax_Syntax.lbtyp);
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___110_5962.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def;
                                 FStar_Syntax_Syntax.lbattrs =
                                   (uu___110_5962.FStar_Syntax_Syntax.lbattrs);
                                 FStar_Syntax_Syntax.lbpos =
                                   (uu___110_5962.FStar_Syntax_Syntax.lbpos)
                               }))
                        in
                     let uu____5963 = FStar_Syntax_Subst.open_let_rec lbs e
                        in
                     (match uu____5963 with
                      | (lbs1,e1) ->
                          let uu____5978 = mapM fflb lbs1  in
                          bind uu____5978
                            (fun lbs2  ->
                               let uu____5990 = ff e1  in
                               bind uu____5990
                                 (fun e2  ->
                                    let uu____5998 =
                                      FStar_Syntax_Subst.close_let_rec lbs2
                                        e2
                                       in
                                    match uu____5998 with
                                    | (lbs3,e3) ->
                                        ret
                                          (FStar_Syntax_Syntax.Tm_let
                                             ((true, lbs3), e3)))))
                 | FStar_Syntax_Syntax.Tm_ascribed (t2,asc,eff) ->
                     let uu____6064 = ff t2  in
                     bind uu____6064
                       (fun t3  ->
                          ret
                            (FStar_Syntax_Syntax.Tm_ascribed (t3, asc, eff)))
                 | FStar_Syntax_Syntax.Tm_meta (t2,m) ->
                     let uu____6093 = ff t2  in
                     bind uu____6093
                       (fun t3  -> ret (FStar_Syntax_Syntax.Tm_meta (t3, m)))
                 | uu____6098 -> ret tn  in
               bind tn1
                 (fun tn2  ->
                    let t' =
                      let uu___111_6105 = t1  in
                      {
                        FStar_Syntax_Syntax.n = tn2;
                        FStar_Syntax_Syntax.pos =
                          (uu___111_6105.FStar_Syntax_Syntax.pos);
                        FStar_Syntax_Syntax.vars =
                          (uu___111_6105.FStar_Syntax_Syntax.vars)
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
            let uu____6134 = FStar_TypeChecker_TcTerm.tc_term env t  in
            match uu____6134 with
            | (t1,lcomp,g) ->
                let uu____6146 =
                  (let uu____6149 =
                     FStar_Syntax_Util.is_pure_or_ghost_lcomp lcomp  in
                   Prims.op_Negation uu____6149) ||
                    (let uu____6151 = FStar_TypeChecker_Rel.is_trivial g  in
                     Prims.op_Negation uu____6151)
                   in
                if uu____6146
                then ret t1
                else
                  (let rewrite_eq =
                     let typ = lcomp.FStar_Syntax_Syntax.res_typ  in
                     let uu____6161 = new_uvar "pointwise_rec" env typ  in
                     bind uu____6161
                       (fun ut  ->
                          log ps
                            (fun uu____6172  ->
                               let uu____6173 =
                                 FStar_Syntax_Print.term_to_string t1  in
                               let uu____6174 =
                                 FStar_Syntax_Print.term_to_string ut  in
                               FStar_Util.print2
                                 "Pointwise_rec: making equality\n\t%s ==\n\t%s\n"
                                 uu____6173 uu____6174);
                          (let uu____6175 =
                             let uu____6178 =
                               let uu____6179 =
                                 FStar_TypeChecker_TcTerm.universe_of env typ
                                  in
                               FStar_Syntax_Util.mk_eq2 uu____6179 typ t1 ut
                                in
                             add_irrelevant_goal "pointwise_rec equation" env
                               uu____6178 opts
                              in
                           bind uu____6175
                             (fun uu____6182  ->
                                let uu____6183 =
                                  bind tau
                                    (fun uu____6189  ->
                                       let ut1 =
                                         FStar_TypeChecker_Normalize.reduce_uvar_solutions
                                           env ut
                                          in
                                       log ps
                                         (fun uu____6195  ->
                                            let uu____6196 =
                                              FStar_Syntax_Print.term_to_string
                                                t1
                                               in
                                            let uu____6197 =
                                              FStar_Syntax_Print.term_to_string
                                                ut1
                                               in
                                            FStar_Util.print2
                                              "Pointwise_rec: succeeded rewriting\n\t%s to\n\t%s\n"
                                              uu____6196 uu____6197);
                                       ret ut1)
                                   in
                                focus uu____6183)))
                      in
                   let uu____6198 = trytac' rewrite_eq  in
                   bind uu____6198
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
          let uu____6346 = FStar_Syntax_Subst.compress t  in
          maybe_continue ctrl uu____6346
            (fun t1  ->
               let uu____6350 =
                 f env
                   (let uu___115_6359 = t1  in
                    {
                      FStar_Syntax_Syntax.n = (t1.FStar_Syntax_Syntax.n);
                      FStar_Syntax_Syntax.pos =
                        (uu___115_6359.FStar_Syntax_Syntax.pos);
                      FStar_Syntax_Syntax.vars =
                        (uu___115_6359.FStar_Syntax_Syntax.vars)
                    })
                  in
               bind uu____6350
                 (fun uu____6371  ->
                    match uu____6371 with
                    | (t2,ctrl1) ->
                        maybe_continue ctrl1 t2
                          (fun t3  ->
                             let uu____6390 =
                               let uu____6391 =
                                 FStar_Syntax_Subst.compress t3  in
                               uu____6391.FStar_Syntax_Syntax.n  in
                             match uu____6390 with
                             | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
                                 let uu____6424 =
                                   ctrl_tac_fold f env ctrl1 hd1  in
                                 bind uu____6424
                                   (fun uu____6449  ->
                                      match uu____6449 with
                                      | (hd2,ctrl2) ->
                                          let ctrl3 = keep_going ctrl2  in
                                          let uu____6465 =
                                            ctrl_tac_fold_args f env ctrl3
                                              args
                                             in
                                          bind uu____6465
                                            (fun uu____6492  ->
                                               match uu____6492 with
                                               | (args1,ctrl4) ->
                                                   ret
                                                     ((let uu___113_6522 = t3
                                                          in
                                                       {
                                                         FStar_Syntax_Syntax.n
                                                           =
                                                           (FStar_Syntax_Syntax.Tm_app
                                                              (hd2, args1));
                                                         FStar_Syntax_Syntax.pos
                                                           =
                                                           (uu___113_6522.FStar_Syntax_Syntax.pos);
                                                         FStar_Syntax_Syntax.vars
                                                           =
                                                           (uu___113_6522.FStar_Syntax_Syntax.vars)
                                                       }), ctrl4)))
                             | FStar_Syntax_Syntax.Tm_abs (bs,t4,k) ->
                                 let uu____6548 =
                                   FStar_Syntax_Subst.open_term bs t4  in
                                 (match uu____6548 with
                                  | (bs1,t') ->
                                      let uu____6563 =
                                        let uu____6570 =
                                          FStar_TypeChecker_Env.push_binders
                                            env bs1
                                           in
                                        ctrl_tac_fold f uu____6570 ctrl1 t'
                                         in
                                      bind uu____6563
                                        (fun uu____6588  ->
                                           match uu____6588 with
                                           | (t'',ctrl2) ->
                                               let uu____6603 =
                                                 let uu____6610 =
                                                   let uu___114_6613 = t4  in
                                                   let uu____6616 =
                                                     let uu____6617 =
                                                       let uu____6634 =
                                                         FStar_Syntax_Subst.close_binders
                                                           bs1
                                                          in
                                                       let uu____6635 =
                                                         FStar_Syntax_Subst.close
                                                           bs1 t''
                                                          in
                                                       (uu____6634,
                                                         uu____6635, k)
                                                        in
                                                     FStar_Syntax_Syntax.Tm_abs
                                                       uu____6617
                                                      in
                                                   {
                                                     FStar_Syntax_Syntax.n =
                                                       uu____6616;
                                                     FStar_Syntax_Syntax.pos
                                                       =
                                                       (uu___114_6613.FStar_Syntax_Syntax.pos);
                                                     FStar_Syntax_Syntax.vars
                                                       =
                                                       (uu___114_6613.FStar_Syntax_Syntax.vars)
                                                   }  in
                                                 (uu____6610, ctrl2)  in
                                               ret uu____6603))
                             | FStar_Syntax_Syntax.Tm_arrow (bs,k) ->
                                 ret (t3, ctrl1)
                             | uu____6668 -> ret (t3, ctrl1))))

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
              let uu____6719 = ctrl_tac_fold f env ctrl t  in
              bind uu____6719
                (fun uu____6747  ->
                   match uu____6747 with
                   | (t1,ctrl1) ->
                       let uu____6766 = ctrl_tac_fold_args f env ctrl1 ts1
                          in
                       bind uu____6766
                         (fun uu____6797  ->
                            match uu____6797 with
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
              let uu____6881 =
                let uu____6888 =
                  add_irrelevant_goal "dummy" env FStar_Syntax_Util.t_true
                    opts
                   in
                bind uu____6888
                  (fun uu____6897  ->
                     let uu____6898 = ctrl t1  in
                     bind uu____6898
                       (fun res  -> bind trivial (fun uu____6925  -> ret res)))
                 in
              bind uu____6881
                (fun uu____6941  ->
                   match uu____6941 with
                   | (should_rewrite,ctrl1) ->
                       if Prims.op_Negation should_rewrite
                       then ret (t1, ctrl1)
                       else
                         (let uu____6965 =
                            FStar_TypeChecker_TcTerm.tc_term env t1  in
                          match uu____6965 with
                          | (t2,lcomp,g) ->
                              let uu____6981 =
                                (let uu____6984 =
                                   FStar_Syntax_Util.is_pure_or_ghost_lcomp
                                     lcomp
                                    in
                                 Prims.op_Negation uu____6984) ||
                                  (let uu____6986 =
                                     FStar_TypeChecker_Rel.is_trivial g  in
                                   Prims.op_Negation uu____6986)
                                 in
                              if uu____6981
                              then ret (t2, globalStop)
                              else
                                (let typ = lcomp.FStar_Syntax_Syntax.res_typ
                                    in
                                 let uu____7001 =
                                   new_uvar "pointwise_rec" env typ  in
                                 bind uu____7001
                                   (fun ut  ->
                                      log ps
                                        (fun uu____7016  ->
                                           let uu____7017 =
                                             FStar_Syntax_Print.term_to_string
                                               t2
                                              in
                                           let uu____7018 =
                                             FStar_Syntax_Print.term_to_string
                                               ut
                                              in
                                           FStar_Util.print2
                                             "Pointwise_rec: making equality\n\t%s ==\n\t%s\n"
                                             uu____7017 uu____7018);
                                      (let uu____7019 =
                                         let uu____7022 =
                                           let uu____7023 =
                                             FStar_TypeChecker_TcTerm.universe_of
                                               env typ
                                              in
                                           FStar_Syntax_Util.mk_eq2
                                             uu____7023 typ t2 ut
                                            in
                                         add_irrelevant_goal
                                           "rewrite_rec equation" env
                                           uu____7022 opts
                                          in
                                       bind uu____7019
                                         (fun uu____7030  ->
                                            let uu____7031 =
                                              bind rewriter
                                                (fun uu____7045  ->
                                                   let ut1 =
                                                     FStar_TypeChecker_Normalize.reduce_uvar_solutions
                                                       env ut
                                                      in
                                                   log ps
                                                     (fun uu____7051  ->
                                                        let uu____7052 =
                                                          FStar_Syntax_Print.term_to_string
                                                            t2
                                                           in
                                                        let uu____7053 =
                                                          FStar_Syntax_Print.term_to_string
                                                            ut1
                                                           in
                                                        FStar_Util.print2
                                                          "rewrite_rec: succeeded rewriting\n\t%s to\n\t%s\n"
                                                          uu____7052
                                                          uu____7053);
                                                   ret (ut1, ctrl1))
                                               in
                                            focus uu____7031))))))
  
let (topdown_rewrite :
  (FStar_Syntax_Syntax.term ->
     (Prims.bool,FStar_BigInt.t) FStar_Pervasives_Native.tuple2 tac)
    -> Prims.unit tac -> Prims.unit tac)
  =
  fun ctrl  ->
    fun rewriter  ->
      bind get
        (fun ps  ->
           let uu____7097 =
             match ps.FStar_Tactics_Types.goals with
             | g::gs -> (g, gs)
             | [] -> failwith "Pointwise: no goals"  in
           match uu____7097 with
           | (g,gs) ->
               let gt1 = g.FStar_Tactics_Types.goal_ty  in
               (log ps
                  (fun uu____7134  ->
                     let uu____7135 = FStar_Syntax_Print.term_to_string gt1
                        in
                     FStar_Util.print1 "Pointwise starting with %s\n"
                       uu____7135);
                bind dismiss_all
                  (fun uu____7138  ->
                     let uu____7139 =
                       ctrl_tac_fold
                         (rewrite_rec ps ctrl rewriter
                            g.FStar_Tactics_Types.opts)
                         g.FStar_Tactics_Types.context keepGoing gt1
                        in
                     bind uu____7139
                       (fun uu____7157  ->
                          match uu____7157 with
                          | (gt',uu____7165) ->
                              (log ps
                                 (fun uu____7169  ->
                                    let uu____7170 =
                                      FStar_Syntax_Print.term_to_string gt'
                                       in
                                    FStar_Util.print1
                                      "Pointwise seems to have succeded with %s\n"
                                      uu____7170);
                               (let uu____7171 = push_goals gs  in
                                bind uu____7171
                                  (fun uu____7175  ->
                                     add_goals
                                       [(let uu___116_7177 = g  in
                                         {
                                           FStar_Tactics_Types.context =
                                             (uu___116_7177.FStar_Tactics_Types.context);
                                           FStar_Tactics_Types.witness =
                                             (uu___116_7177.FStar_Tactics_Types.witness);
                                           FStar_Tactics_Types.goal_ty = gt';
                                           FStar_Tactics_Types.opts =
                                             (uu___116_7177.FStar_Tactics_Types.opts);
                                           FStar_Tactics_Types.is_guard =
                                             (uu___116_7177.FStar_Tactics_Types.is_guard)
                                         })])))))))
  
let (pointwise :
  FStar_Tactics_Types.direction -> Prims.unit tac -> Prims.unit tac) =
  fun d  ->
    fun tau  ->
      bind get
        (fun ps  ->
           let uu____7199 =
             match ps.FStar_Tactics_Types.goals with
             | g::gs -> (g, gs)
             | [] -> failwith "Pointwise: no goals"  in
           match uu____7199 with
           | (g,gs) ->
               let gt1 = g.FStar_Tactics_Types.goal_ty  in
               (log ps
                  (fun uu____7236  ->
                     let uu____7237 = FStar_Syntax_Print.term_to_string gt1
                        in
                     FStar_Util.print1 "Pointwise starting with %s\n"
                       uu____7237);
                bind dismiss_all
                  (fun uu____7240  ->
                     let uu____7241 =
                       tac_fold_env d
                         (pointwise_rec ps tau g.FStar_Tactics_Types.opts)
                         g.FStar_Tactics_Types.context gt1
                        in
                     bind uu____7241
                       (fun gt'  ->
                          log ps
                            (fun uu____7251  ->
                               let uu____7252 =
                                 FStar_Syntax_Print.term_to_string gt'  in
                               FStar_Util.print1
                                 "Pointwise seems to have succeded with %s\n"
                                 uu____7252);
                          (let uu____7253 = push_goals gs  in
                           bind uu____7253
                             (fun uu____7257  ->
                                add_goals
                                  [(let uu___117_7259 = g  in
                                    {
                                      FStar_Tactics_Types.context =
                                        (uu___117_7259.FStar_Tactics_Types.context);
                                      FStar_Tactics_Types.witness =
                                        (uu___117_7259.FStar_Tactics_Types.witness);
                                      FStar_Tactics_Types.goal_ty = gt';
                                      FStar_Tactics_Types.opts =
                                        (uu___117_7259.FStar_Tactics_Types.opts);
                                      FStar_Tactics_Types.is_guard =
                                        (uu___117_7259.FStar_Tactics_Types.is_guard)
                                    })]))))))
  
let (trefl : Prims.unit tac) =
  bind cur_goal
    (fun g  ->
       let uu____7279 =
         FStar_Syntax_Util.un_squash g.FStar_Tactics_Types.goal_ty  in
       match uu____7279 with
       | FStar_Pervasives_Native.Some t ->
           let uu____7291 = FStar_Syntax_Util.head_and_args' t  in
           (match uu____7291 with
            | (hd1,args) ->
                let uu____7324 =
                  let uu____7337 =
                    let uu____7338 = FStar_Syntax_Util.un_uinst hd1  in
                    uu____7338.FStar_Syntax_Syntax.n  in
                  (uu____7337, args)  in
                (match uu____7324 with
                 | (FStar_Syntax_Syntax.Tm_fvar
                    fv,uu____7352::(l,uu____7354)::(r,uu____7356)::[]) when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.eq2_lid
                     ->
                     let uu____7403 =
                       do_unify g.FStar_Tactics_Types.context l r  in
                     bind uu____7403
                       (fun b  ->
                          if Prims.op_Negation b
                          then
                            let uu____7412 =
                              tts g.FStar_Tactics_Types.context l  in
                            let uu____7413 =
                              tts g.FStar_Tactics_Types.context r  in
                            fail2 "trefl: not a trivial equality (%s vs %s)"
                              uu____7412 uu____7413
                          else solve g FStar_Syntax_Util.exp_unit)
                 | (hd2,uu____7416) ->
                     let uu____7433 = tts g.FStar_Tactics_Types.context t  in
                     fail1 "trefl: not an equality (%s)" uu____7433))
       | FStar_Pervasives_Native.None  -> fail "not an irrelevant goal")
  
let (dup : Prims.unit tac) =
  bind cur_goal
    (fun g  ->
       let uu____7443 =
         new_uvar "dup" g.FStar_Tactics_Types.context
           g.FStar_Tactics_Types.goal_ty
          in
       bind uu____7443
         (fun u  ->
            let g' =
              let uu___118_7450 = g  in
              {
                FStar_Tactics_Types.context =
                  (uu___118_7450.FStar_Tactics_Types.context);
                FStar_Tactics_Types.witness = u;
                FStar_Tactics_Types.goal_ty =
                  (uu___118_7450.FStar_Tactics_Types.goal_ty);
                FStar_Tactics_Types.opts =
                  (uu___118_7450.FStar_Tactics_Types.opts);
                FStar_Tactics_Types.is_guard =
                  (uu___118_7450.FStar_Tactics_Types.is_guard)
              }  in
            bind __dismiss
              (fun uu____7453  ->
                 let uu____7454 =
                   let uu____7457 =
                     let uu____7458 =
                       FStar_TypeChecker_TcTerm.universe_of
                         g.FStar_Tactics_Types.context
                         g.FStar_Tactics_Types.goal_ty
                        in
                     FStar_Syntax_Util.mk_eq2 uu____7458
                       g.FStar_Tactics_Types.goal_ty u
                       g.FStar_Tactics_Types.witness
                      in
                   add_irrelevant_goal "dup equation"
                     g.FStar_Tactics_Types.context uu____7457
                     g.FStar_Tactics_Types.opts
                    in
                 bind uu____7454
                   (fun uu____7461  ->
                      let uu____7462 = add_goals [g']  in
                      bind uu____7462 (fun uu____7466  -> ret ())))))
  
let (flip : Prims.unit tac) =
  bind get
    (fun ps  ->
       match ps.FStar_Tactics_Types.goals with
       | g1::g2::gs ->
           set
             (let uu___119_7485 = ps  in
              {
                FStar_Tactics_Types.main_context =
                  (uu___119_7485.FStar_Tactics_Types.main_context);
                FStar_Tactics_Types.main_goal =
                  (uu___119_7485.FStar_Tactics_Types.main_goal);
                FStar_Tactics_Types.all_implicits =
                  (uu___119_7485.FStar_Tactics_Types.all_implicits);
                FStar_Tactics_Types.goals = (g2 :: g1 :: gs);
                FStar_Tactics_Types.smt_goals =
                  (uu___119_7485.FStar_Tactics_Types.smt_goals);
                FStar_Tactics_Types.depth =
                  (uu___119_7485.FStar_Tactics_Types.depth);
                FStar_Tactics_Types.__dump =
                  (uu___119_7485.FStar_Tactics_Types.__dump);
                FStar_Tactics_Types.psc =
                  (uu___119_7485.FStar_Tactics_Types.psc);
                FStar_Tactics_Types.entry_range =
                  (uu___119_7485.FStar_Tactics_Types.entry_range);
                FStar_Tactics_Types.guard_policy =
                  (uu___119_7485.FStar_Tactics_Types.guard_policy)
              })
       | uu____7486 -> fail "flip: less than 2 goals")
  
let (later : Prims.unit tac) =
  bind get
    (fun ps  ->
       match ps.FStar_Tactics_Types.goals with
       | [] -> ret ()
       | g::gs ->
           set
             (let uu___120_7503 = ps  in
              {
                FStar_Tactics_Types.main_context =
                  (uu___120_7503.FStar_Tactics_Types.main_context);
                FStar_Tactics_Types.main_goal =
                  (uu___120_7503.FStar_Tactics_Types.main_goal);
                FStar_Tactics_Types.all_implicits =
                  (uu___120_7503.FStar_Tactics_Types.all_implicits);
                FStar_Tactics_Types.goals = (FStar_List.append gs [g]);
                FStar_Tactics_Types.smt_goals =
                  (uu___120_7503.FStar_Tactics_Types.smt_goals);
                FStar_Tactics_Types.depth =
                  (uu___120_7503.FStar_Tactics_Types.depth);
                FStar_Tactics_Types.__dump =
                  (uu___120_7503.FStar_Tactics_Types.__dump);
                FStar_Tactics_Types.psc =
                  (uu___120_7503.FStar_Tactics_Types.psc);
                FStar_Tactics_Types.entry_range =
                  (uu___120_7503.FStar_Tactics_Types.entry_range);
                FStar_Tactics_Types.guard_policy =
                  (uu___120_7503.FStar_Tactics_Types.guard_policy)
              }))
  
let (qed : Prims.unit tac) =
  bind get
    (fun ps  ->
       match ps.FStar_Tactics_Types.goals with
       | [] -> ret ()
       | uu____7512 -> fail "Not done!")
  
let (cases :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 tac)
  =
  fun t  ->
    let uu____7530 =
      bind cur_goal
        (fun g  ->
           let uu____7544 = __tc g.FStar_Tactics_Types.context t  in
           bind uu____7544
             (fun uu____7580  ->
                match uu____7580 with
                | (t1,typ,guard) ->
                    let uu____7596 = FStar_Syntax_Util.head_and_args typ  in
                    (match uu____7596 with
                     | (hd1,args) ->
                         let uu____7639 =
                           let uu____7652 =
                             let uu____7653 = FStar_Syntax_Util.un_uinst hd1
                                in
                             uu____7653.FStar_Syntax_Syntax.n  in
                           (uu____7652, args)  in
                         (match uu____7639 with
                          | (FStar_Syntax_Syntax.Tm_fvar
                             fv,(p,uu____7672)::(q,uu____7674)::[]) when
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
                                let uu___121_7712 = g  in
                                let uu____7713 =
                                  FStar_TypeChecker_Env.push_bv
                                    g.FStar_Tactics_Types.context v_p
                                   in
                                {
                                  FStar_Tactics_Types.context = uu____7713;
                                  FStar_Tactics_Types.witness =
                                    (uu___121_7712.FStar_Tactics_Types.witness);
                                  FStar_Tactics_Types.goal_ty =
                                    (uu___121_7712.FStar_Tactics_Types.goal_ty);
                                  FStar_Tactics_Types.opts =
                                    (uu___121_7712.FStar_Tactics_Types.opts);
                                  FStar_Tactics_Types.is_guard =
                                    (uu___121_7712.FStar_Tactics_Types.is_guard)
                                }  in
                              let g2 =
                                let uu___122_7715 = g  in
                                let uu____7716 =
                                  FStar_TypeChecker_Env.push_bv
                                    g.FStar_Tactics_Types.context v_q
                                   in
                                {
                                  FStar_Tactics_Types.context = uu____7716;
                                  FStar_Tactics_Types.witness =
                                    (uu___122_7715.FStar_Tactics_Types.witness);
                                  FStar_Tactics_Types.goal_ty =
                                    (uu___122_7715.FStar_Tactics_Types.goal_ty);
                                  FStar_Tactics_Types.opts =
                                    (uu___122_7715.FStar_Tactics_Types.opts);
                                  FStar_Tactics_Types.is_guard =
                                    (uu___122_7715.FStar_Tactics_Types.is_guard)
                                }  in
                              bind __dismiss
                                (fun uu____7723  ->
                                   let uu____7724 = add_goals [g1; g2]  in
                                   bind uu____7724
                                     (fun uu____7733  ->
                                        let uu____7734 =
                                          let uu____7739 =
                                            FStar_Syntax_Syntax.bv_to_name
                                              v_p
                                             in
                                          let uu____7740 =
                                            FStar_Syntax_Syntax.bv_to_name
                                              v_q
                                             in
                                          (uu____7739, uu____7740)  in
                                        ret uu____7734))
                          | uu____7745 ->
                              let uu____7758 =
                                tts g.FStar_Tactics_Types.context typ  in
                              fail1 "Not a disjunction: %s" uu____7758))))
       in
    FStar_All.pipe_left (wrap_err "cases") uu____7530
  
let (set_options : Prims.string -> Prims.unit tac) =
  fun s  ->
    bind cur_goal
      (fun g  ->
         FStar_Options.push ();
         (let uu____7796 = FStar_Util.smap_copy g.FStar_Tactics_Types.opts
             in
          FStar_Options.set uu____7796);
         (let res = FStar_Options.set_options FStar_Options.Set s  in
          let opts' = FStar_Options.peek ()  in
          FStar_Options.pop ();
          (match res with
           | FStar_Getopt.Success  ->
               let g' =
                 let uu___123_7803 = g  in
                 {
                   FStar_Tactics_Types.context =
                     (uu___123_7803.FStar_Tactics_Types.context);
                   FStar_Tactics_Types.witness =
                     (uu___123_7803.FStar_Tactics_Types.witness);
                   FStar_Tactics_Types.goal_ty =
                     (uu___123_7803.FStar_Tactics_Types.goal_ty);
                   FStar_Tactics_Types.opts = opts';
                   FStar_Tactics_Types.is_guard =
                     (uu___123_7803.FStar_Tactics_Types.is_guard)
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
  FStar_Reflection_Data.typ ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac)
  =
  fun ty  ->
    fun tm  ->
      let uu____7847 =
        bind cur_goal
          (fun goal  ->
             let env =
               FStar_TypeChecker_Env.set_expected_typ
                 goal.FStar_Tactics_Types.context ty
                in
             let uu____7855 = __tc env tm  in
             bind uu____7855
               (fun uu____7875  ->
                  match uu____7875 with
                  | (tm1,typ,guard) ->
                      let uu____7887 =
                        proc_guard "unquote" env guard
                          goal.FStar_Tactics_Types.opts
                         in
                      bind uu____7887 (fun uu____7891  -> ret tm1)))
         in
      FStar_All.pipe_left (wrap_err "unquote") uu____7847
  
let (uvar_env :
  env ->
    FStar_Reflection_Data.typ FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.term tac)
  =
  fun env  ->
    fun ty  ->
      let uu____7910 =
        match ty with
        | FStar_Pervasives_Native.Some ty1 -> ret ty1
        | FStar_Pervasives_Native.None  ->
            let uu____7916 =
              let uu____7917 = FStar_Syntax_Util.type_u ()  in
              FStar_All.pipe_left FStar_Pervasives_Native.fst uu____7917  in
            new_uvar "uvar_env.2" env uu____7916
         in
      bind uu____7910
        (fun typ  ->
           let uu____7929 = new_uvar "uvar_env" env typ  in
           bind uu____7929 (fun t  -> ret t))
  
let (unshelve : FStar_Syntax_Syntax.term -> Prims.unit tac) =
  fun t  ->
    let uu____7941 =
      bind get
        (fun ps  ->
           let env = ps.FStar_Tactics_Types.main_context  in
           let opts =
             match ps.FStar_Tactics_Types.goals with
             | g::uu____7952 -> g.FStar_Tactics_Types.opts
             | uu____7955 -> FStar_Options.peek ()  in
           let uu____7958 = __tc env t  in
           bind uu____7958
             (fun uu____7978  ->
                match uu____7978 with
                | (t1,typ,guard) ->
                    let uu____7990 = proc_guard "unshelve" env guard opts  in
                    bind uu____7990
                      (fun uu____7995  ->
                         let uu____7996 =
                           let uu____7999 =
                             let uu____8000 = bnorm env t1  in
                             let uu____8001 = bnorm env typ  in
                             {
                               FStar_Tactics_Types.context = env;
                               FStar_Tactics_Types.witness = uu____8000;
                               FStar_Tactics_Types.goal_ty = uu____8001;
                               FStar_Tactics_Types.opts = opts;
                               FStar_Tactics_Types.is_guard = false
                             }  in
                           [uu____7999]  in
                         add_goals uu____7996)))
       in
    FStar_All.pipe_left (wrap_err "unshelve") uu____7941
  
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
          (fun uu____8034  ->
             let uu____8035 = FStar_Options.unsafe_tactic_exec ()  in
             if uu____8035
             then
               let s =
                 FStar_Util.launch_process true "tactic_launch" prog args
                   input (fun uu____8041  -> fun uu____8042  -> false)
                  in
               ret s
             else
               fail
                 "launch_process: will not run anything unless --unsafe_tactic_exec is provided")
  
let (fresh_bv_named :
  Prims.string -> FStar_Reflection_Data.typ -> FStar_Syntax_Syntax.bv tac) =
  fun nm  ->
    fun t  ->
      bind idtac
        (fun uu____8056  ->
           let uu____8057 =
             FStar_Syntax_Syntax.gen_bv nm FStar_Pervasives_Native.None t  in
           ret uu____8057)
  
let (change : FStar_Reflection_Data.typ -> Prims.unit tac) =
  fun ty  ->
    let uu____8065 =
      mlog
        (fun uu____8070  ->
           let uu____8071 = FStar_Syntax_Print.term_to_string ty  in
           FStar_Util.print1 "change: ty = %s\n" uu____8071)
        (fun uu____8073  ->
           bind cur_goal
             (fun g  ->
                let uu____8077 = __tc g.FStar_Tactics_Types.context ty  in
                bind uu____8077
                  (fun uu____8097  ->
                     match uu____8097 with
                     | (ty1,uu____8107,guard) ->
                         let uu____8109 =
                           proc_guard "change" g.FStar_Tactics_Types.context
                             guard g.FStar_Tactics_Types.opts
                            in
                         bind uu____8109
                           (fun uu____8114  ->
                              let uu____8115 =
                                do_unify g.FStar_Tactics_Types.context
                                  g.FStar_Tactics_Types.goal_ty ty1
                                 in
                              bind uu____8115
                                (fun bb  ->
                                   if bb
                                   then
                                     replace_cur
                                       (let uu___124_8124 = g  in
                                        {
                                          FStar_Tactics_Types.context =
                                            (uu___124_8124.FStar_Tactics_Types.context);
                                          FStar_Tactics_Types.witness =
                                            (uu___124_8124.FStar_Tactics_Types.witness);
                                          FStar_Tactics_Types.goal_ty = ty1;
                                          FStar_Tactics_Types.opts =
                                            (uu___124_8124.FStar_Tactics_Types.opts);
                                          FStar_Tactics_Types.is_guard =
                                            (uu___124_8124.FStar_Tactics_Types.is_guard)
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
                                      let uu____8131 =
                                        do_unify
                                          g.FStar_Tactics_Types.context ng
                                          nty
                                         in
                                      bind uu____8131
                                        (fun b  ->
                                           if b
                                           then
                                             replace_cur
                                               (let uu___125_8140 = g  in
                                                {
                                                  FStar_Tactics_Types.context
                                                    =
                                                    (uu___125_8140.FStar_Tactics_Types.context);
                                                  FStar_Tactics_Types.witness
                                                    =
                                                    (uu___125_8140.FStar_Tactics_Types.witness);
                                                  FStar_Tactics_Types.goal_ty
                                                    = ty1;
                                                  FStar_Tactics_Types.opts =
                                                    (uu___125_8140.FStar_Tactics_Types.opts);
                                                  FStar_Tactics_Types.is_guard
                                                    =
                                                    (uu___125_8140.FStar_Tactics_Types.is_guard)
                                                })
                                           else fail "not convertible")))))))
       in
    FStar_All.pipe_left (wrap_err "change") uu____8065
  
let rec last : 'a . 'a Prims.list -> 'a =
  fun l  ->
    match l with
    | [] -> failwith "last: empty list"
    | x::[] -> x
    | uu____8159::xs -> last xs
  
let rec init : 'a . 'a Prims.list -> 'a Prims.list =
  fun l  ->
    match l with
    | [] -> failwith "init: empty list"
    | x::[] -> []
    | x::xs -> let uu____8184 = init xs  in x :: uu____8184
  
let rec (inspect :
  FStar_Syntax_Syntax.term -> FStar_Reflection_Data.term_view tac) =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t  in
    let t2 = FStar_Syntax_Util.un_uinst t1  in
    match t2.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_meta (t3,uu____8199) -> inspect t3
    | FStar_Syntax_Syntax.Tm_name bv ->
        FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_Var bv)
    | FStar_Syntax_Syntax.Tm_bvar bv ->
        FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_BVar bv)
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_FVar fv)
    | FStar_Syntax_Syntax.Tm_app (hd1,[]) ->
        failwith "inspect: empty arguments on Tm_app"
    | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
        let uu____8256 = last args  in
        (match uu____8256 with
         | (a,q) ->
             let q' = FStar_Reflection_Basic.inspect_aqual q  in
             let uu____8278 =
               let uu____8279 =
                 let uu____8284 =
                   let uu____8287 =
                     let uu____8288 = init args  in
                     FStar_Syntax_Syntax.mk_Tm_app hd1 uu____8288  in
                   uu____8287 FStar_Pervasives_Native.None
                     t2.FStar_Syntax_Syntax.pos
                    in
                 (uu____8284, (a, q'))  in
               FStar_Reflection_Data.Tv_App uu____8279  in
             FStar_All.pipe_left ret uu____8278)
    | FStar_Syntax_Syntax.Tm_abs ([],uu____8309,uu____8310) ->
        failwith "inspect: empty arguments on Tm_abs"
    | FStar_Syntax_Syntax.Tm_abs (bs,t3,k) ->
        let uu____8354 = FStar_Syntax_Subst.open_term bs t3  in
        (match uu____8354 with
         | (bs1,t4) ->
             (match bs1 with
              | [] -> failwith "impossible"
              | b::bs2 ->
                  let uu____8387 =
                    let uu____8388 =
                      let uu____8393 = FStar_Syntax_Util.abs bs2 t4 k  in
                      (b, uu____8393)  in
                    FStar_Reflection_Data.Tv_Abs uu____8388  in
                  FStar_All.pipe_left ret uu____8387))
    | FStar_Syntax_Syntax.Tm_type uu____8400 ->
        FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_Type ())
    | FStar_Syntax_Syntax.Tm_arrow ([],k) ->
        failwith "inspect: empty binders on arrow"
    | FStar_Syntax_Syntax.Tm_arrow uu____8420 ->
        let uu____8433 = FStar_Syntax_Util.arrow_one t2  in
        (match uu____8433 with
         | FStar_Pervasives_Native.Some (b,c) ->
             FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_Arrow (b, c))
         | FStar_Pervasives_Native.None  -> failwith "impossible")
    | FStar_Syntax_Syntax.Tm_refine (bv,t3) ->
        let b = FStar_Syntax_Syntax.mk_binder bv  in
        let uu____8463 = FStar_Syntax_Subst.open_term [b] t3  in
        (match uu____8463 with
         | (b',t4) ->
             let b1 =
               match b' with
               | b'1::[] -> b'1
               | uu____8494 -> failwith "impossible"  in
             FStar_All.pipe_left ret
               (FStar_Reflection_Data.Tv_Refine
                  ((FStar_Pervasives_Native.fst b1), t4)))
    | FStar_Syntax_Syntax.Tm_constant c ->
        let uu____8502 =
          let uu____8503 = FStar_Reflection_Basic.inspect_const c  in
          FStar_Reflection_Data.Tv_Const uu____8503  in
        FStar_All.pipe_left ret uu____8502
    | FStar_Syntax_Syntax.Tm_uvar (u,t3) ->
        let uu____8532 =
          let uu____8533 =
            let uu____8538 =
              let uu____8539 = FStar_Syntax_Unionfind.uvar_id u  in
              FStar_BigInt.of_int_fs uu____8539  in
            (uu____8538, t3)  in
          FStar_Reflection_Data.Tv_Uvar uu____8533  in
        FStar_All.pipe_left ret uu____8532
    | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),t21) ->
        if lb.FStar_Syntax_Syntax.lbunivs <> []
        then FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
        else
          (match lb.FStar_Syntax_Syntax.lbname with
           | FStar_Util.Inr uu____8567 ->
               FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
           | FStar_Util.Inl bv ->
               let b = FStar_Syntax_Syntax.mk_binder bv  in
               let uu____8572 = FStar_Syntax_Subst.open_term [b] t21  in
               (match uu____8572 with
                | (bs,t22) ->
                    let b1 =
                      match bs with
                      | b1::[] -> b1
                      | uu____8603 ->
                          failwith
                            "impossible: open_term returned different amount of binders"
                       in
                    FStar_All.pipe_left ret
                      (FStar_Reflection_Data.Tv_Let
                         (false, (FStar_Pervasives_Native.fst b1),
                           (lb.FStar_Syntax_Syntax.lbdef), t22))))
    | FStar_Syntax_Syntax.Tm_let ((true ,lb::[]),t21) ->
        if lb.FStar_Syntax_Syntax.lbunivs <> []
        then FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
        else
          (match lb.FStar_Syntax_Syntax.lbname with
           | FStar_Util.Inr uu____8635 ->
               FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
           | FStar_Util.Inl bv ->
               let uu____8639 = FStar_Syntax_Subst.open_let_rec [lb] t21  in
               (match uu____8639 with
                | (lbs,t22) ->
                    (match lbs with
                     | lb1::[] ->
                         (match lb1.FStar_Syntax_Syntax.lbname with
                          | FStar_Util.Inr uu____8659 ->
                              ret FStar_Reflection_Data.Tv_Unknown
                          | FStar_Util.Inl bv1 ->
                              FStar_All.pipe_left ret
                                (FStar_Reflection_Data.Tv_Let
                                   (true, bv1,
                                     (lb1.FStar_Syntax_Syntax.lbdef), t22)))
                     | uu____8665 ->
                         failwith
                           "impossible: open_term returned different amount of binders")))
    | FStar_Syntax_Syntax.Tm_match (t3,brs) ->
        let rec inspect_pat p =
          match p.FStar_Syntax_Syntax.v with
          | FStar_Syntax_Syntax.Pat_constant c ->
              let uu____8717 = FStar_Reflection_Basic.inspect_const c  in
              FStar_Reflection_Data.Pat_Constant uu____8717
          | FStar_Syntax_Syntax.Pat_cons (fv,ps) ->
              let uu____8736 =
                let uu____8743 =
                  FStar_List.map
                    (fun uu____8755  ->
                       match uu____8755 with
                       | (p1,uu____8763) -> inspect_pat p1) ps
                   in
                (fv, uu____8743)  in
              FStar_Reflection_Data.Pat_Cons uu____8736
          | FStar_Syntax_Syntax.Pat_var bv ->
              FStar_Reflection_Data.Pat_Var bv
          | FStar_Syntax_Syntax.Pat_wild bv ->
              FStar_Reflection_Data.Pat_Wild bv
          | FStar_Syntax_Syntax.Pat_dot_term (bv,t4) ->
              FStar_Reflection_Data.Pat_Dot_Term (bv, t4)
           in
        let brs1 = FStar_List.map FStar_Syntax_Subst.open_branch brs  in
        let brs2 =
          FStar_List.map
            (fun uu___61_8817  ->
               match uu___61_8817 with
               | (pat,uu____8839,t4) ->
                   let uu____8857 = inspect_pat pat  in (uu____8857, t4))
            brs1
           in
        FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_Match (t3, brs2))
    | FStar_Syntax_Syntax.Tm_unknown  ->
        FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
    | uu____8874 ->
        ((let uu____8876 =
            let uu____8881 =
              let uu____8882 = FStar_Syntax_Print.tag_of_term t2  in
              let uu____8883 = FStar_Syntax_Print.term_to_string t2  in
              FStar_Util.format2
                "inspect: outside of expected syntax (%s, %s)\n" uu____8882
                uu____8883
               in
            (FStar_Errors.Warning_CantInspect, uu____8881)  in
          FStar_Errors.log_issue t2.FStar_Syntax_Syntax.pos uu____8876);
         FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown)
  
let (pack : FStar_Reflection_Data.term_view -> FStar_Syntax_Syntax.term tac)
  =
  fun tv  ->
    match tv with
    | FStar_Reflection_Data.Tv_Var bv ->
        let uu____8894 = FStar_Syntax_Syntax.bv_to_name bv  in
        FStar_All.pipe_left ret uu____8894
    | FStar_Reflection_Data.Tv_BVar bv ->
        let uu____8898 = FStar_Syntax_Syntax.bv_to_tm bv  in
        FStar_All.pipe_left ret uu____8898
    | FStar_Reflection_Data.Tv_FVar fv ->
        let uu____8902 = FStar_Syntax_Syntax.fv_to_tm fv  in
        FStar_All.pipe_left ret uu____8902
    | FStar_Reflection_Data.Tv_App (l,(r,q)) ->
        let q' = FStar_Reflection_Basic.pack_aqual q  in
        let uu____8913 = FStar_Syntax_Util.mk_app l [(r, q')]  in
        FStar_All.pipe_left ret uu____8913
    | FStar_Reflection_Data.Tv_Abs (b,t) ->
        let uu____8934 =
          FStar_Syntax_Util.abs [b] t FStar_Pervasives_Native.None  in
        FStar_All.pipe_left ret uu____8934
    | FStar_Reflection_Data.Tv_Arrow (b,c) ->
        let uu____8939 = FStar_Syntax_Util.arrow [b] c  in
        FStar_All.pipe_left ret uu____8939
    | FStar_Reflection_Data.Tv_Type () ->
        FStar_All.pipe_left ret FStar_Syntax_Util.ktype
    | FStar_Reflection_Data.Tv_Refine (bv,t) ->
        let uu____8960 = FStar_Syntax_Util.refine bv t  in
        FStar_All.pipe_left ret uu____8960
    | FStar_Reflection_Data.Tv_Const c ->
        let uu____8972 =
          let uu____8975 =
            let uu____8978 =
              let uu____8979 = FStar_Reflection_Basic.pack_const c  in
              FStar_Syntax_Syntax.Tm_constant uu____8979  in
            FStar_Syntax_Syntax.mk uu____8978  in
          uu____8975 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
        FStar_All.pipe_left ret uu____8972
    | FStar_Reflection_Data.Tv_Uvar (u,t) ->
        let uu____8993 =
          let uu____8996 = FStar_BigInt.to_int_fs u  in
          FStar_Syntax_Util.uvar_from_id uu____8996 t  in
        FStar_All.pipe_left ret uu____8993
    | FStar_Reflection_Data.Tv_Let (false ,bv,t1,t2) ->
        let lb =
          FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl bv) []
            bv.FStar_Syntax_Syntax.sort FStar_Parser_Const.effect_Tot_lid t1
            [] FStar_Range.dummyRange
           in
        let uu____9011 =
          let uu____9014 =
            let uu____9017 =
              let uu____9018 =
                let uu____9031 =
                  let uu____9032 =
                    let uu____9033 = FStar_Syntax_Syntax.mk_binder bv  in
                    [uu____9033]  in
                  FStar_Syntax_Subst.close uu____9032 t2  in
                ((false, [lb]), uu____9031)  in
              FStar_Syntax_Syntax.Tm_let uu____9018  in
            FStar_Syntax_Syntax.mk uu____9017  in
          uu____9014 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
        FStar_All.pipe_left ret uu____9011
    | FStar_Reflection_Data.Tv_Let (true ,bv,t1,t2) ->
        let lb =
          FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl bv) []
            bv.FStar_Syntax_Syntax.sort FStar_Parser_Const.effect_Tot_lid t1
            [] FStar_Range.dummyRange
           in
        let uu____9059 = FStar_Syntax_Subst.open_let_rec [lb] t2  in
        (match uu____9059 with
         | (lbs_open,body_open) ->
             let uu____9074 = FStar_Syntax_Subst.close_let_rec [lb] body_open
                in
             (match uu____9074 with
              | (lbs,body) ->
                  let uu____9089 =
                    FStar_Syntax_Syntax.mk
                      (FStar_Syntax_Syntax.Tm_let ((true, lbs), body))
                      FStar_Pervasives_Native.None FStar_Range.dummyRange
                     in
                  FStar_All.pipe_left ret uu____9089))
    | FStar_Reflection_Data.Tv_Match (t,brs) ->
        let wrap v1 =
          {
            FStar_Syntax_Syntax.v = v1;
            FStar_Syntax_Syntax.p = FStar_Range.dummyRange
          }  in
        let rec pack_pat p =
          match p with
          | FStar_Reflection_Data.Pat_Constant c ->
              let uu____9125 =
                let uu____9126 = FStar_Reflection_Basic.pack_const c  in
                FStar_Syntax_Syntax.Pat_constant uu____9126  in
              FStar_All.pipe_left wrap uu____9125
          | FStar_Reflection_Data.Pat_Cons (fv,ps) ->
              let uu____9135 =
                let uu____9136 =
                  let uu____9149 =
                    FStar_List.map
                      (fun p1  ->
                         let uu____9163 = pack_pat p1  in (uu____9163, false))
                      ps
                     in
                  (fv, uu____9149)  in
                FStar_Syntax_Syntax.Pat_cons uu____9136  in
              FStar_All.pipe_left wrap uu____9135
          | FStar_Reflection_Data.Pat_Var bv ->
              FStar_All.pipe_left wrap (FStar_Syntax_Syntax.Pat_var bv)
          | FStar_Reflection_Data.Pat_Wild bv ->
              FStar_All.pipe_left wrap (FStar_Syntax_Syntax.Pat_wild bv)
          | FStar_Reflection_Data.Pat_Dot_Term (bv,t1) ->
              FStar_All.pipe_left wrap
                (FStar_Syntax_Syntax.Pat_dot_term (bv, t1))
           in
        let brs1 =
          FStar_List.map
            (fun uu___62_9213  ->
               match uu___62_9213 with
               | (pat,t1) ->
                   let uu____9230 = pack_pat pat  in
                   (uu____9230, FStar_Pervasives_Native.None, t1)) brs
           in
        let brs2 = FStar_List.map FStar_Syntax_Subst.close_branch brs1  in
        let uu____9240 =
          FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_match (t, brs2))
            FStar_Pervasives_Native.None FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____9240
    | FStar_Reflection_Data.Tv_AscribedT (e,t,tacopt) ->
        let uu____9260 =
          FStar_Syntax_Syntax.mk
            (FStar_Syntax_Syntax.Tm_ascribed
               (e, ((FStar_Util.Inl t), tacopt),
                 FStar_Pervasives_Native.None)) FStar_Pervasives_Native.None
            FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____9260
    | FStar_Reflection_Data.Tv_AscribedC (e,c,tacopt) ->
        let uu____9302 =
          FStar_Syntax_Syntax.mk
            (FStar_Syntax_Syntax.Tm_ascribed
               (e, ((FStar_Util.Inr c), tacopt),
                 FStar_Pervasives_Native.None)) FStar_Pervasives_Native.None
            FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____9302
    | FStar_Reflection_Data.Tv_Unknown  ->
        let uu____9337 =
          FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
            FStar_Pervasives_Native.None FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____9337
  
let (goal_of_goal_ty :
  env ->
    FStar_Reflection_Data.typ ->
      (FStar_Tactics_Types.goal,FStar_TypeChecker_Env.guard_t)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun typ  ->
      let uu____9362 =
        FStar_TypeChecker_Util.new_implicit_var "proofstate_of_goal_ty"
          typ.FStar_Syntax_Syntax.pos env typ
         in
      match uu____9362 with
      | (u,uu____9380,g_u) ->
          let g =
            let uu____9395 = FStar_Options.peek ()  in
            {
              FStar_Tactics_Types.context = env;
              FStar_Tactics_Types.witness = u;
              FStar_Tactics_Types.goal_ty = typ;
              FStar_Tactics_Types.opts = uu____9395;
              FStar_Tactics_Types.is_guard = false
            }  in
          (g, g_u)
  
let (proofstate_of_goal_ty :
  env ->
    FStar_Reflection_Data.typ ->
      (FStar_Tactics_Types.proofstate,FStar_Syntax_Syntax.term)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun typ  ->
      let uu____9406 = goal_of_goal_ty env typ  in
      match uu____9406 with
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
  